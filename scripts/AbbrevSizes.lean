import Lean
open Lean Meta

/-!
Lists the type synonyms declared with `abbrev` in the given modules, with the size of each body
counted two ways: as a tree, with every shared subterm counted once per occurrence, and as it
sits in memory, with each distinct subterm counted once. One tab-separated line per synonym,
largest tree first:

    name  module  tree-size  in-memory  own-instances  uses  unfolds-to

A type synonym declared with `abbrev` has no instances of its own: instance search unfolds it
and uses those of the type it stands for, so every instance term spells out the body again.
When the body mentions another such synonym, its instances mention that one's body, and so on:
the tree size multiplies at every level while the in-memory size stays small, because Lean
shares the repeated subterms. Parts of Lean walk terms as trees (see #5362, #5398), so a large
first number next to a small second one marks a synonym that should become a `def` with its own
instances (`inferInstanceAs`), as `AGENTS.md` asks.

- `own-instances` counts the instances whose conclusion is about the synonym itself (its name
  is the head of an argument of the class), for example `instance : Module ℂ (Foo G)`;
- `uses` counts the declarations of the given modules whose statement mentions the synonym;
- `unfolds-to` is the head of the body, after its `fun` binders and `let`s.

    lake env lean --run scripts/AbbrevSizes.lean RiemannMasullo.AppD_SchwartzBruhat.Sec1b ...

With `--min N` as the first argument only synonyms whose tree size is at least `N` are listed.
Use `scripts/abbrev_sizes.sh`, which builds first and passes every module of the library.
-/

/-- The size of `e` as a tree. Memoized on the subterm, so that the walk itself takes time
proportional to the size in memory, not to the result. -/
partial def treeSize (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some v := (← get)[e]? then return v
  let v ← match e with
    | .app f a => pure (1 + (← treeSize f) + (← treeSize a))
    | .lam _ d b _ | .forallE _ d b _ => pure (1 + (← treeSize d) + (← treeSize b))
    | .letE _ t v b _ => pure (1 + (← treeSize t) + (← treeSize v) + (← treeSize b))
    | .proj _ _ x | .mdata _ x => pure (1 + (← treeSize x))
    | _ => pure 1
  modify (·.insert e v)
  return v

/-- The number of distinct subterms of `e`. -/
def dagSize (e : Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut stack := #[e]
  while h : stack.size > 0 do
    let e := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains e then continue
    seen := seen.insert e
    match e with
    | .app f a => stack := stack.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => stack := stack.push t |>.push b
    | .letE _ t v b _ => stack := stack.push t |>.push v |>.push b
    | .proj _ _ x | .mdata _ x => stack := stack.push x
    | _ => pure ()
  return seen.size

/-- The head constant of a body, after its `fun` binders, `let`s and metadata. -/
partial def bodyHead : Expr → Name
  | .lam _ _ b _ | .letE _ _ _ b _ | .mdata _ b => bodyHead b
  | e => e.getAppFn.constName?.getD `_

/-- Whether a declaration's type ends in `Sort u` other than `Prop`, read off syntactically. -/
partial def endsInType : Expr → Bool
  | .forallE _ _ b _ | .mdata _ b => endsInType b
  | .sort u => !u.isZero
  | _ => false

def main (args : List String) : IO UInt32 := do
  let (minSize, args) := match args with
    | "--min" :: n :: rest => (n.toNat!, rest)
    | _ => (0, args)
  initSearchPath (← findSysroot)
  let modules := args.toArray.map (·.toName)
  let env ← importModules (modules.map ({ module := · })) {} (trustLevel := 1024)
  let wanted : Std.HashSet Name := Std.HashSet.ofArray modules
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)
  let inWanted (n : Name) : Bool := (moduleOf n).any wanted.contains
  -- `abbrev` makes a definition reducible and inline; instances are reducible too.
  let mut synonyms : Array (Name × DefinitionVal) := #[]
  for (n, c) in env.constants.toList do
    let .defnInfo d := c | continue
    if n.isInternalDetail || !inWanted n then continue
    unless getReducibilityStatusCore env n == .reducible do continue
    if isInstanceCore env n then continue
    unless (Compiler.getInlineAttribute? env n).isSome do continue
    unless endsInType d.type do continue
    synonyms := synonyms.push (n, d)
  let names : Std.HashSet Name := Std.HashSet.ofArray (synonyms.map (·.1))
  -- Instances about each synonym, from anywhere in the environment.
  let ctx : Core.Context := { fileName := "<AbbrevSizes>", fileMap := default, maxHeartbeats := 0 }
  let (own, _) ← MetaM.toIO (ctxCore := ctx) (sCore := { env }) do
    let mut own : Std.HashMap Name Nat := {}
    for (n, c) in env.constants.toList do
      unless isInstanceCore env n do continue
      let heads ← forallTelescope c.type fun _ b =>
        return b.getAppArgs.filterMap (·.getAppFn.constName?)
      for h in heads.toList.eraseDups do
        if names.contains h then own := own.insert h (own.getD h 0 + 1)
    return own
  -- Declarations of the given modules whose statement mentions each synonym.
  let mut uses : Std.HashMap Name Nat := {}
  for (n, c) in env.constants.toList do
    if n.isInternalDetail || !inWanted n then continue
    for k in c.type.getUsedConstants do
      if names.contains k then uses := uses.insert k (uses.getD k 0 + 1)
  let mut rows : Array (Nat × String) := #[]
  for (n, d) in synonyms do
    let value := d.value
    let tree := (treeSize value).run' {} |>.run
    if tree < minSize then continue
    let mod := (moduleOf n).getD .anonymous
    rows := rows.push (tree,
      s!"{n}\t{mod}\t{tree}\t{dagSize value}\t{own.getD n 0}\t{uses.getD n 0}\t{bodyHead value}")
  for (_, line) in rows.qsort (fun a b => a.1 > b.1 || (a.1 == b.1 && a.2 < b.2)) do
    IO.println line
  return 0
