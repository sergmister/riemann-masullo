import Lean.Elab.Import

open Lean

private def gitOutput (args : Array String) : IO String := do
  let result ← IO.Process.output { cmd := "git", args := #["-c", "core.fsmonitor=false"] ++ args }
  if result.exitCode != 0 then
    throw (IO.userError result.stderr.trimAscii.toString)
  return result.stdout

private def importAllModules (path source : String) : IO (Option (Array Name)) := do
  -- Parse the file header only. Do not import modules or elaborate the candidate.
  let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext source path)
  if messages.hasErrors then
    return none
  return some <| (Elab.HeaderSyntax.imports header false).filterMap fun entry =>
    if entry.importAll then some entry.module else none

private def checkFiles (base candidate : String) : List String → IO UInt32
  | status :: path :: rest => do
    let mut added := false
    if path.endsWith ".lean" && !path.startsWith "RiemannMasullo/External/" then
      let old ← if status == "A" then pure #[] else do
        let some imports ← importAllModules path (← gitOutput #["cat-file", "blob", s!"{base}:{path}"])
          | throw (IO.userError s!"could not parse the Lean import header in main's {path}")
        pure imports
      let some new ← importAllModules path (← gitOutput #["cat-file", "blob", s!"{candidate}:{path}"])
        | IO.eprintln s!"{path}: invalid Lean import header"
          return 4
      for mod in new do
        unless old.contains mod do
          let display := (toString mod).replace "@" "＠" |>.replace "`" "｀" |>.replace "\n" " "
          IO.println s!"{path}: new `import all {display}`"
          added := true
    let later ← checkFiles base candidate rest
    return if added && later == 0 then 3 else later
  | [] | [""] => pure 0
  | _ => throw (IO.userError "invalid changed-file list from git")

/-- Compare the exact candidate tree with its current main base. Return 3 for a new `import all`,
4 for an invalid candidate header, and 2 for a checker error. -/
def main (args : List String) : IO UInt32 := do
  let [base, candidate] := args
    | IO.eprintln "usage: lean --run scripts/CheckImportAll.lean BASE CANDIDATE"
      return 2
  try
    let changes ← gitOutput #["diff", "--name-status", "-z", "--diff-filter=AM", "--no-renames", "--no-ext-diff",
      base, candidate, "--", "RiemannMasullo/"]
    checkFiles base candidate (changes.splitOn (String.singleton (Char.ofNat 0)))
  catch e =>
    IO.eprintln s!"import check: {e}"
    return 2
