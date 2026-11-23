#!/usr/bin/env python3
"""Rebuild the proof-progress page from the current checkout and the live issue tracker.

    python3 scripts/progress/build.py

That one command is all there is: it runs `lake build RiemannMasullo`, reads the issues with
`gh`, and writes `.agent/progress/index.html` (one self-contained file; `.agent/` is ignored
by git). It changes nothing else: no git command that writes, no issue is touched. It can be
rerun at any time, also while pull requests are being merged into the checkout: if `HEAD`
moves or an `.olean` is missing halfway through, it starts over.

    --out PATH      write the page somewhere else
    --no-build      skip `lake build` and trust the existing build (sorries then come from the
                    Lean environment instead of the build warnings)
    --stats         also print per-section counts

Where the data comes from

* Sections and proof issues: `gh issue list --label section|proof --state all`.
* Contributors: the authors of merged pull requests (`gh pr list --state merged`), leaving out
  the repository owner, whose account the project's own agents push from, and bots.
* Which theorems still have a `sorry`: the `declaration uses sorry` warnings of
  `lake build RiemannMasullo`, as in `scripts/issues.py`, cross-checked against the terms.
* Dependencies: `scripts/progress/Deps.lean` loads the built library with `importModules` at
  `OLeanLevel.private`, so proof terms are visible, and lists for every constant the project
  constants in its type and in its body. Nothing is guessed from the source text. Auxiliary
  constants (`foo._proof_1`, structure projections, anonymous instances, ...) are folded into
  the declaration a person wrote.
* Waves that are not seeded yet: the Roadmap table of `README.md` and the table of contents at
  the top of `paper/the-music-of-the-primes.txt`.

Each run also appends one line of totals to `history.jsonl` next to the page (skipped when
nothing changed since the last line); the page shows the change since the previous line. The
chart of proof issues over time is drawn from the issues' own timestamps, so it covers the
whole history of the project and not only the runs of this script.

Before anything is written the numbers are checked against each other; if they do not add up,
or the build or `gh` fails, the existing page is left as it was and the exit status is 1.

Layout is a function of structure only (issue numbers, `needs` markers, source order), never
of state, so a section or declaration stays where it is while the proof fills in.
"""
import argparse, collections, datetime, json, os, pathlib, re, subprocess, sys, tempfile, time

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
HERE = pathlib.Path(__file__).resolve().parent
LIB = "RiemannMasullo"
WARN = re.compile(r"warning: (RiemannMasullo/\S+?\.lean):(\d+):(\d+): declaration uses `sorry`")
SORRY_MARK = re.compile(r"<!-- sorry: (\S+) -->")
NEEDS_MARK = re.compile(r"<!-- needs:([\d\s]*)-->")
KEYWORD = re.compile(r"\b(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\b")
PAPER = re.compile(r"Paper:\s*(.*?),?\s*pp?\.\s*(\d+)(?:\s*[-–]\s*(\d+))?\.?\s*", re.S)
NUMBER = re.compile(r"(?:[A-E]|\d+)(?:\.\d+)+")


class Retry(Exception):
    """The checkout moved under us, or a build product was not there yet."""


def run(cmd, check=True, **kw):
    out = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, **kw)
    if check and out.returncode:
        raise RuntimeError(f"{' '.join(cmd[:4])} failed:\n{(out.stdout + out.stderr)[-2000:]}")
    return out


def note(notes, text):
    if text not in notes:
        notes.append(text)


# ---------------------------------------------------------------------------------------------
# Inputs


def git_head():
    return run(["git", "rev-parse", "HEAD"]).stdout.strip()


def gh_json(args):
    for attempt in range(3):
        out = run(["gh"] + args, check=False)
        if out.returncode == 0:
            return json.loads(out.stdout)
        time.sleep(3 * (attempt + 1))
    raise RuntimeError("gh failed: " + out.stderr[-500:])


def fetch_issues():
    fields = "number,title,state,labels,body,assignees,createdAt,closedAt"

    def get(label, limit):
        # The REST listing, page by page: `gh issue list` with a label goes through GitHub's
        # search and stops at 1,000 results. While issues are being opened the pages shift and
        # one issue can come back twice; keep one copy of each.
        shape = ('.[] | select(.pull_request | not) | {number, title, state: (.state | ascii_upcase), '
                 'labels: [.labels[] | {name}], body, assignees: [.assignees[] | {login}], '
                 'createdAt: .created_at, closedAt: .closed_at} | tojson')
        for attempt in range(3):
            out = run(["gh", "api", "--paginate",
                       f"repos/{{owner}}/{{repo}}/issues?state=all&labels={label}&per_page=100",
                       "--jq", shape], check=False)
            if out.returncode == 0:
                break
            time.sleep(3 * (attempt + 1))
        else:
            raise RuntimeError("gh failed: " + out.stderr[-500:])
        listing = [json.loads(line) for line in out.stdout.splitlines() if line.strip()]
        return sorted({i["number"]: i for i in listing}.values(), key=lambda i: i["number"])

    repo = gh_json(["repo", "view", "--json", "url,nameWithOwner,owner"])
    return repo, get("section", 1000), get("proof", 20000)


def fetch_contributions(repo):
    """Merged pull requests by people other than the repository owner, oldest first:
    [login, merged-at in Unix seconds, number]."""
    owner = repo["owner"]["login"]
    pulls = gh_json(["pr", "list", "--state", "merged", "--limit", "100000",
                     "--json", "number,author,mergedAt"])
    stamp = lambda s: int(datetime.datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp())
    rows = [[p["author"]["login"], stamp(p["mergedAt"]), p["number"]] for p in pulls
            if p.get("author") and p.get("mergedAt") and not p["author"].get("is_bot")
            and p["author"]["login"] != owner]
    return sorted(rows, key=lambda r: (r[1], r[2]))


def lake_build():
    """Build the library; return {(path, line, col)} of `declaration uses sorry` warnings."""
    out = run(["lake", "build", LIB], check=False)
    if out.returncode:
        raise Retry("lake build failed:\n" + (out.stdout + out.stderr)[-1500:])
    return {(p, int(l), int(c)) for p, l, c in WARN.findall(out.stdout + out.stderr)}


def lean_constants(modules):
    out = run(["lake", "env", "lean", "--run", str(HERE / "Deps.lean")] + modules, check=False)
    if out.returncode:
        raise Retry("Deps.lean failed:\n" + (out.stdout + out.stderr)[-1500:])
    rows = []
    for line in out.stdout.splitlines():
        if line.startswith("{"):
            rows.append(json.loads(line))
    if not rows:
        raise Retry("Deps.lean printed nothing")
    return rows


def module_files():
    files = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / LIB).rglob("*.lean"))
    return {f[:-5].replace("/", "."): f for f in files}


# ---------------------------------------------------------------------------------------------
# Paper: table of contents and roadmap


def parse_toc():
    """Chapters and sections with their page ranges, from the top of the text extraction."""
    path = ROOT / "paper" / "the-music-of-the-primes.txt"
    chapters, sections, pending = [], [], None
    try:
        with open(path, encoding="utf-8", errors="replace") as fh:
            lines = [next(fh, "") for _ in range(220)]
    except OSError:
        return {}, {}
    for line in lines:
        line = line.replace("\f", "").rstrip()
        m = re.match(r"\s*(?:Chapter\s+(\d+)|Appendix\s+([A-E]))\.\s+(.*?)\s{2,}(\d+)$", line)
        if m:
            key = f"ch{int(m.group(1)):02d}" if m.group(1) else "app" + m.group(2)
            chapters.append(dict(key=key, title=m.group(3).strip(), start=int(m.group(4))))
            pending = None
            continue
        m = re.match(r"\s*((?:\d+|[A-E])\.\d+)\.\s+(.*?)(?:\s{2,}(\d+))?$", line)
        if m and m.group(3):
            sections.append(dict(num=m.group(1), title=m.group(2).strip(), start=int(m.group(3))))
            pending = None
        elif m:
            pending = dict(num=m.group(1), title=m.group(2).strip())
        elif pending and (m := re.search(r"\s{2,}(\d+)$", line)):
            sections.append(dict(pending, start=int(m.group(1))))
            pending = None
    seen, order = set(), []
    for c in chapters:                      # running heads can repeat a line
        if c["key"] not in seen:
            seen.add(c["key"]); order.append(c)
    order.sort(key=lambda c: c["start"])
    last = 940
    for c, nxt in zip(order, order[1:] + [None]):
        c["end"] = (nxt["start"] - 1) if nxt else last
    by_key = {c["key"]: c for c in order}
    secs = {}
    for s in sections:
        head = s["num"].split(".")[0]
        ck = f"ch{int(head):02d}" if head.isdigit() else "app" + head
        if ck in by_key and s["num"] not in secs:
            secs[s["num"]] = dict(s, chapter=ck)
    ordered = sorted(secs.values(), key=lambda s: s["start"])
    for s, nxt in zip(ordered, ordered[1:] + [None]):
        end = by_key[s["chapter"]]["end"]
        if nxt and nxt["chapter"] == s["chapter"]:
            end = max(s["start"], nxt["start"] - 1)
        s["end"] = end
    for c in order:
        c["sections"] = [s["num"] for s in ordered if s["chapter"] == c["key"]]
    return by_key, secs


def chapter_label(key):
    return f"Ch. {int(key[2:])}" if key.startswith("ch") else f"App. {key[3:]}"


def chapter_sort(key):
    """Appendices (the foundations) first, then chapters in order."""
    return (0, key[3:]) if key.startswith("app") else (1, f"{int(key[2:]):03d}")


def parse_roadmap(toc_chapters, toc_sections):
    """Rows of the Roadmap table in README.md, with the chapters each one names."""
    try:
        text = (ROOT / "README.md").read_text(encoding="utf-8")
    except OSError:
        return [], ""
    status = ""
    m = re.search(r"^## Status\s+(.*?)(?=^## )", text, re.S | re.M)
    if m and (b := re.search(r"\*\*(.+?)\*\*", m.group(1))):
        status = b.group(1).strip().rstrip(".")
    m = re.search(r"^## Roadmap\s+(.*?)(?=^## |\Z)", text, re.S | re.M)
    waves = []
    if not m:
        return waves, status
    unlink = lambda s: re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", s).strip()
    for line in m.group(1).splitlines():
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if not line.strip().startswith("|") or len(cells) < 3 or set(cells[0]) <= set("-: ") \
                or cells[0].lower() == "wave":
            continue
        name, paper, state = unlink(cells[0]), unlink(cells[1]), unlink(cells[2])
        flat = paper.replace("–", "-")
        parts = collections.OrderedDict()           # chapter key -> None (whole) | [section nums]
        item, sep = r"\d+(?:-\d+)?", r"(?:\s*,\s*|\s+and\s+)"
        for g in re.finditer(rf"Chapters?\s+({item}(?:{sep}{item})*)", flat):
            for part in re.split(sep, g.group(1)):
                a, _, b = part.partition("-")
                for n in range(int(a), int(b or a) + 1):
                    parts[f"ch{n:02d}"] = None
        for g in re.finditer(r"\b([A-E])\.(\d+)(?:-(?:[A-E]\.)?(\d+))?", flat):
            key = "app" + g.group(1)
            if key in parts and parts[key] is None:
                continue
            for n in range(int(g.group(2)), int(g.group(3) or g.group(2)) + 1):
                parts.setdefault(key, []).append(f"{g.group(1)}.{n}")
        for g in re.finditer(r"Appendi(?:x|ces)\s+([^;:()]*)", flat):
            for tok in re.split(sep, g.group(1)):
                if re.fullmatch(r"[A-E]", tok.strip()):
                    parts["app" + tok.strip()] = None
        chapters = []
        for key, secs in parts.items():
            c = toc_chapters.get(key)
            if c:
                chapters.append(dict(key=key, title=c["title"], whole=secs is None,
                                     nums=list(c["sections"]) if secs is None else
                                     [s for s in secs if s in toc_sections]))
        waves.append(dict(name=name if name.lower().startswith(("wave", "later")) or not name.isdigit()
                          else f"Wave {name}", text=paper, status=state, chapters=chapters))
    for w in waves:
        if w["name"].lower() == "later":
            w["name"] = "Later"
    return waves, status


def wave_part(part, seeded, toc_chapters, toc_sections):
    """What is left of one chapter of a wave once the sections with an issue are taken out."""
    left = [n for n in part["nums"] if n not in seeded]
    if not left:
        return None
    c = toc_chapters[part["key"]]
    if part["whole"] and len(left) == len(part["nums"]):
        label, pages = chapter_label(part["key"]), [[c["start"], c["end"]]]
    else:
        label = chapter_label(part["key"]) + " §" + compress_nums(left)
        pages = []
        for n in left:
            a, b = toc_sections[n]["start"], toc_sections[n]["end"]
            if pages and a <= pages[-1][1] + 1:
                pages[-1][1] = max(pages[-1][1], b)
            else:
                pages.append([a, b])
    return dict(key=part["key"], label=label, title=c["title"], pages=pages, sections=len(left))


def compress_nums(nums):
    """['B.1','B.2','B.3','B.6'] -> 'B.1–B.3, B.6'."""
    out, run_ = [], []
    flush = lambda: out.append(run_[0] if len(run_) == 1 else f"{run_[0]}–{run_[-1]}") if run_ else None
    for n in nums:
        if run_ and int(n.split(".")[1]) == int(run_[-1].split(".")[1]) + 1:
            run_.append(n)
        else:
            flush(); run_ = [n]
    flush()
    return ", ".join(out)


# ---------------------------------------------------------------------------------------------
# Declarations


def private_stripped(name):
    """`_private.Mod.Ule.0.Ns.foo` -> `Ns.foo`."""
    if name.startswith("_private."):
        m = re.match(r"_private\..*?\.0\.(.*)$", name)
        if m:
            return m.group(1)
    return name


def display_name(name):
    name = private_stripped(name)
    return name[len(LIB) + 1:] if name.startswith(LIB + ".") else name


def paper_item(doc):
    """Split a docstring `Paper: Lemma A.2.3.4(2), p. 549. Text` into item, page and text."""
    m = PAPER.match(doc or "")
    if not m:
        return None
    raw = " ".join(m.group(1).split())
    rest = " ".join(doc[m.end():].split())
    num = NUMBER.search(raw)
    if not num:
        return dict(key=raw, label=raw, number="", page=int(m.group(2)), text=rest, raw=raw)
    before = raw[:num.start()]
    number = num.group(0)
    if before.endswith("("):
        label, kind = f"({number})", "eq"
    elif before.endswith("§"):
        label, kind = f"§{number}", "text"
    else:
        words = re.findall(r"[A-Za-z]+", before)
        word = words[-1] if words else ""
        word = {"Equations": "Equation", "Definitions": "Definition", "Lemmas": "Lemma"}.get(word, word)
        label, kind = (f"{word} {number}" if word else number), word.lower() or "item"
    return dict(key=f"{kind}:{number}", label=label, number=number, page=int(m.group(2)),
                text=rest, raw=raw)


def excerpt(text, limit=260):
    text = " ".join((text or "").split())
    if len(text) <= limit:
        return text
    cut = text[:limit].rsplit(" ", 1)[0]
    return cut.rstrip(",;:") + " …"


class Library:
    """The user-written declarations of the library and how they depend on each other."""

    def __init__(self, rows, files, notes):
        self.notes = notes
        self.rows = {r["n"]: r for r in rows}
        self.files = files                                   # module -> path
        self.src = {}
        self.user = {}                                       # name -> declaration dict
        self._find_user_declarations()
        self._owners()
        self._dependencies()

    def lines(self, module):
        if module not in self.src:
            path = self.files.get(module)
            if not path:
                raise Retry(f"no source file for module {module}")
            self.src[module] = (ROOT / path).read_text(encoding="utf-8").split("\n")
        return self.src[module]

    def _find_user_declarations(self):
        """A constant is something a person wrote when a declaration keyword stands between the
        start of its range and its name. That leaves out projections, constructors, anonymous
        instances, notation and everything the elaborator generates."""
        for name, r in self.rows.items():
            if "r" not in r or "sel" not in r:
                continue
            L = self.lines(r["m"])
            (l0, c0, _l1, _c1), (sl, sc) = r["r"], r["sel"]
            if sl > len(L) or l0 > len(L):
                raise Retry(f"{r['m']} is shorter than its build says")
            head = L[l0 - 1][c0:sc] if sl == l0 else "\n".join(
                [L[l0 - 1][c0:]] + L[l0:sl - 1] + [L[sl - 1][:sc]])
            head = re.sub(r"/--.*?-/", "", head, flags=re.S)
            kws = KEYWORD.findall(head)
            if not kws:
                continue
            tok = re.match(r"[^\s:({\[]+", L[sl - 1][sc:])
            tok = tok.group(0) if tok else ""        # as scripts/issues.py reads the name
            plain = tok.rstrip(".").replace("«", "").replace("»", "")   # `foo.{u}` leaves `foo.`
            plain = plain.removeprefix("_root_.")   # `theorem _root_.Foo.bar` declares `Foo.bar`
            if not plain or not private_stripped(name).replace("«", "").replace("»", "").endswith(plain):
                note(self.notes, f"{self.files[r['m']]}:{sl} should name `{display_name(name)}` but "
                                 f"reads `{tok}`; its source link may be off.")
            kw = kws[-1]
            if r["k"] == "theorem":
                kind = "theorem"
            elif kw in ("theorem", "lemma"):
                kind = "def"            # a `theorem` whose type is not a Prop cannot happen
            else:
                kind = kw
            self.user[name] = dict(
                name=name, show=display_name(name), kind=kind, module=r["m"], mi=r.get("mi", 0),
                path=self.files[r["m"]], line=sl, col=sc, start=l0, token=tok,
                private="private" in head.split(), doc=r.get("doc", ""))

    def _owners(self):
        """Map every auxiliary constant to the user declaration it belongs to, if any."""
        self.owner = {}
        for name, r in self.rows.items():
            if name in self.user:
                continue
            if r.get("of") in self.user:
                self.owner[name] = r["of"]
                continue
            for cand in (name, private_stripped(name)):
                parts = cand.split(".")
                found = None
                for i in range(len(parts) - 1, 0, -1):
                    prefix = ".".join(parts[:i])
                    if prefix in self.user:
                        found = prefix
                        break
                if found:
                    self.owner[name] = found
                    break
        self.aux_of = collections.defaultdict(list)
        for aux, own in self.owner.items():
            self.aux_of[own].append(aux)

    def _closure(self, me, start):
        """User declarations reached from the constants in `start`, looking through `me`'s own
        auxiliary constants and through constants nobody owns (anonymous instances and the
        like). Returns (declarations, whether a `sorry` hides in something looked through)."""
        found, seen, hidden, todo = set(), set(), False, list(start)
        while todo:
            c = todo.pop()
            if c in seen or c == me:
                continue
            seen.add(c)
            if c in self.user:
                found.add(c)
                continue
            r = self.rows.get(c)
            if r is None:
                continue
            own = self.owner.get(c)
            if own is not None and own != me:
                found.add(own)
                continue
            if r.get("s") and own is None:
                hidden = True
            todo.extend(r.get("t", []))
            todo.extend(r.get("v", []))
        return found, hidden

    def _dependencies(self):
        for name, d in self.user.items():
            r = self.rows[name]
            stmt_start = list(r.get("t", []))
            proof_start = []
            if d["kind"] == "theorem":
                proof_start = list(r.get("v", []))
            else:
                stmt_start += r.get("v", [])
                for aux in self.aux_of.get(name, []):       # fields of a structure, and so on
                    if self.rows[aux]["k"] in ("constructor",):
                        stmt_start += self.rows[aux].get("t", [])
            stmt, hid1 = self._closure(name, stmt_start)
            proof, hid2 = self._closure(name, proof_start)
            d["stmt"] = sorted(stmt)
            d["proof"] = sorted(proof - stmt)
            d["hidden_sorry"] = hid1 or hid2
            d["sorry_term"] = bool(r.get("s")) or any(
                self.rows[a].get("s") for a in self.aux_of.get(name, []))

    def mark_sorries(self, warnings):
        """Decide which declarations have a `sorry`. Lean's build warnings are the authority when
        there was a build; the terms are the cross-check (and the fallback for --no-build)."""
        at = {(d["path"], d["line"], d["col"]): n for n, d in self.user.items()}
        if warnings is None:
            for d in self.user.values():
                d["sorry"] = d["sorry_term"]
            return
        warned = set()
        for path, line, col in sorted(warnings):
            n = at.get((path, line, col))
            if n is None:       # fall back to the declaration whose range holds the position
                inside = [m for m, d in self.user.items()
                          if d["path"] == path and d["start"] <= line <= self.rows[m]["r"][2]]
                n = inside[0] if len(inside) == 1 else None
            if n is None:
                note(self.notes, f"`sorry` outside a named declaration at {path}:{line} "
                                 "(an anonymous instance?); it has no node on this page.")
            else:
                warned.add(n)
        for n, d in self.user.items():
            d["sorry"] = n in warned
            if d["sorry"] != d["sorry_term"]:
                note(self.notes, f"`{d['show']}`: the build {'reports' if d['sorry'] else 'does not report'}"
                                 f" a sorry but its term {'has none' if d['sorry'] else 'has one'}.")
            if d["sorry"] and d["kind"] != "theorem":
                note(self.notes, f"`{d['show']}` is a {d['kind']} with a `sorry` inside, "
                                 "which AGENTS.md forbids.")

    def rest_on_sorry(self):
        """Set `open_below`, the number of distinct sorried declarations each one depends on,
        transitively. Returns the declarations in source order."""
        order = sorted(self.user, key=lambda n: (self.user[n]["mi"], self.user[n]["line"]))
        below = {}
        for n in order:                 # source order is a topological order
            d = self.user[n]
            acc = set()
            for dep in d["stmt"] + d["proof"]:
                if dep not in below:    # a forward reference inside a mutual block
                    continue
                acc |= below[dep]
                if self.user[dep]["sorry"]:
                    acc.add(dep)
                d["hidden_sorry"] = d["hidden_sorry"] or self.user[dep]["hidden_sorry"]
            below[n] = acc
            d["open_below"] = len(acc)
        return order


# ---------------------------------------------------------------------------------------------
# Sections


def section_meta(issue):
    title = issue["title"]
    m = re.match(r"\s*(§\s*\S+)\s*(.*)$", title)
    num, rest = (m.group(1), m.group(2)) if m else ("#%d" % issue["number"], title)
    pages = []
    pm = re.search(r"\(pp?\.\s*([^)]*)\)\s*$", rest)
    if pm:
        rest = rest[:pm.start()].strip()
        for a, b in re.findall(r"(\d+)(?:\s*[-–]\s*(\d+))?", pm.group(1)):
            pages.append([int(a), int(b or a)])
    head = re.match(r"§\s*([A-E]|\d+)\.", num)
    labels = [l["name"] for l in issue["labels"]]
    if head:
        chapter = f"ch{int(head.group(1)):02d}" if head.group(1).isdigit() else "app" + head.group(1)
    else:
        chapter = next((l for l in labels if re.fullmatch(r"ch\d\d|app[A-E]", l)), "other")
    body = issue["body"] or ""
    nm = NEEDS_MARK.search(body)
    needs = [int(x) for x in nm.group(1).split()] if nm else []
    # The issue's own "Target" line says which file it is for, whatever the file is called (the
    # bridge to the Comparator targets, #5630, is `Targets.lean`, and its body also mentions the
    # `Sec4.lean` it builds on). Issues without such a line are read as before.
    named = re.search(r"^- \*\*Target\*\*:(.*)$", body, re.M)
    targets = re.findall(r"RiemannMasullo/(\w+)/(\w+?)…?\.lean", named.group(1)) if named else []
    targets = targets or re.findall(r"RiemannMasullo/(\w+)/(Sec\w*?)…?\.lean", body)
    subs = []
    sm = re.search(r"\*\*Subsections\*\*:\s*(.*)", body)
    if sm:
        for part in sm.group(1).split(" · "):
            g = re.match(r"\s*((?:[A-E]|\d+)(?:\.\d+)+)\s+(.*?)\s*$", part)
            if g:
                subs.append([g.group(1), g.group(2)])
    claimed = "claimed" in labels or bool(issue["assignees"])
    if issue["state"] == "CLOSED":
        state = "stated"
    elif claimed:
        # Also when it is still labelled `blocked`: a digester may start on top of statements
        # that are in review, before the sections it needs are closed.
        state = "digesting"
    elif "blocked" in labels:
        state = "blocked"
    else:
        state = "ready"
    return dict(id=issue["number"], num=num.replace("§ ", "§"), title=rest, pages=pages,
                chapter=chapter, needs=needs, targets=targets, subs=subs, state=state,
                labels=labels)


def assign_modules(sections, files, lib, notes):
    """Give every source module to the section whose target file name is the longest prefix of
    its own (`Sec2a_part2.lean` belongs with `Sec2a.lean`). ForMathlib is its own group."""
    owner = {}
    for module, path in files.items():
        parts = path.split("/")
        if len(parts) < 3:
            continue                                       # chapter index files
        if parts[1] == "ForMathlib":
            owner[module] = "formathlib"
            continue
        if parts[1] == "External":
            owner[module] = "external"
            continue
        stem, best = parts[-1][:-5], None
        for s in sections:
            for d, t in s["targets"]:
                if d == parts[1] and stem.startswith(t) and (best is None or len(t) > best[0]):
                    best = (len(t), s["id"])
        if best:
            owner[module] = best[1]
    # Cross-check with the page numbers in the docstrings, and place files no target names.
    for module in files:
        pages = [p["page"] for d in lib.user.values() if d["module"] == module
                 for p in [paper_item(d["doc"])] if p]
        votes = collections.Counter()
        for pg in pages:
            for s in sections:
                if any(a <= pg <= b for a, b in s["pages"]):
                    votes[s["id"]] += 1
        if module not in owner:
            if not any(d["module"] == module for d in lib.user.values()):
                continue
            if votes:
                owner[module] = votes.most_common(1)[0][0]
                note(notes, f"{files[module]} matches no section's target file; placed with "
                            f"#{owner[module]} by the page numbers in its docstrings.")
            else:
                owner[module] = "other"
                note(notes, f"{files[module]} belongs to no section issue; shown under Other files.")
        elif isinstance(owner[module], int) and pages and votes.get(owner[module], 0) < len(pages) / 2:
            top = votes.most_common(1)
            note(notes, f"{files[module]} is filed under #{owner[module]} by its name, but most of its "
                        f"page references fall in " + (f"#{top[0][0]}" if top else "no section") + ".")
    return owner


def layout_sections(sections, lanes):
    """Rows for the overview: a section sits below everything it needs, and no two sections of
    one chapter share a row. Depends only on the `needs` markers and the issue numbers."""
    by_id = {s["id"]: s for s in sections}
    lane_of = {k: i for i, k in enumerate(lanes)}
    row, taken = {}, set()
    pending = sorted(by_id)
    while pending:
        progressed = False
        for sid in list(pending):
            s = by_id[sid]
            needs = [n for n in s["needs"] if n in by_id]
            if any(n not in row for n in needs):
                continue
            r = 1 + max((row[n] for n in needs), default=-1)
            while (lane_of[s["chapter"]], r) in taken:
                r += 1
            row[sid] = r
            taken.add((lane_of[s["chapter"]], r))
            pending.remove(sid)
            progressed = True
        if not progressed:                                  # a cycle in the markers
            for sid in pending:
                row[sid] = 1 + max(row.values(), default=-1)
            break
    for s in sections:
        s["lane"], s["row"] = lane_of[s["chapter"]], row[s["id"]]


def group_items(names, lib, by_file):
    """Group declarations into the nodes of one diagram: by the paper item their docstring
    cites, or by source file for ForMathlib. Returns (items in source order, item of each)."""
    items, item_of = collections.OrderedDict(), {}

    def put(key, n, **first):
        items.setdefault(key, dict(decls=[], **first))["decls"].append(n)
        item_of[n] = key

    if by_file:
        for n in names:
            path = lib.user[n]["path"]
            put("file:" + path, n, label=path.split("/", 2)[-1][:-5], number="", page=None)
        return items, item_of
    # A declaration without a paper reference is a helper. It goes with the next declaration
    # of its file that has one, since helpers stand just before what they support, and at the
    # end of a file with the last one.
    per_file = collections.OrderedDict()
    for n in names:
        per_file.setdefault(lib.user[n]["module"], []).append(n)
    for module, ns in per_file.items():
        following, nxt = {}, None
        for n in reversed(ns):
            nxt = lib.user[n]["paper"] or nxt
            following[n] = nxt
        last = next((lib.user[n]["paper"] for n in reversed(ns) if lib.user[n]["paper"]), None)
        for n in ns:
            p = following[n] or last
            if p:
                put(p["key"], n, label=p["label"], number=p["number"], page=p["page"])
            else:
                put("helpers:" + module, n, label="Helper lemmas", number="", page=None)
    return items, item_of


def transitive_reduction(nodes, deps):
    """deps[a] = set of things a depends on (a DAG). Returns the edges (a, b) that no longer
    path from a to b makes redundant."""
    memo = {}

    def reach(a):
        if a not in memo:
            memo[a] = set()
            acc = set()
            for b in deps.get(a, ()):
                acc.add(b)
                acc |= reach(b)
            memo[a] = acc
        return memo[a]

    keep = []
    for a in nodes:
        direct = deps.get(a, set())
        for b in sorted(direct):
            if not any(b in reach(c) for c in direct if c != b):
                keep.append((a, b))
    return keep


# ---------------------------------------------------------------------------------------------
# Assembling the page data


def build_model(repo, section_issues, proof_issues, rows, files, warnings, head):
    notes = []
    lib = Library(rows, files, notes)
    lib.mark_sorries(warnings)
    order = lib.rest_on_sorry()
    toc_chapters, toc_sections = parse_toc()
    waves, readme_status = parse_roadmap(toc_chapters, toc_sections)

    sections = sorted((section_meta(i) for i in section_issues), key=lambda s: s["id"])
    by_id = {s["id"]: s for s in sections}
    owner = assign_modules(sections, files, lib, notes)

    # Proof issues, keyed the way scripts/issues.py keys them: path::name-as-written.
    issues = collections.defaultdict(list)
    for i in proof_issues:
        m = SORRY_MARK.search(i["body"] or "")
        if not m:
            note(notes, f"Proof issue #{i['number']} has no `sorry:` marker.")
            continue
        labels = [l["name"] for l in i["labels"]]
        issues[m.group(1)].append(dict(
            number=i["number"], open=i["state"] == "OPEN",
            claimed="claimed" in labels or bool(i["assignees"]),
            who=[a["login"] for a in i["assignees"]]))
    keys = collections.Counter(f"{d['path']}::{d['token']}" for d in lib.user.values())
    matched = set()

    # Groups: one per section issue, plus ForMathlib and anything unplaced.
    groups = collections.OrderedDict()
    for s in sections:
        groups[s["id"]] = dict(s, key=f"section-{s['id']}", decls=[])
    extra_titles = {"formathlib": ("ForMathlib", "General lemmas missing from Mathlib"),
                    "external": ("External", "Vendored third-party Lean"),
                    "other": ("Other files", "Files that belong to no section issue")}
    index = {}
    decls = []
    for n in order:
        d = lib.user[n]
        g = owner.get(d["module"], "other")
        if g not in groups:
            num, title = extra_titles.get(g, (str(g), ""))
            groups[g] = dict(id=None, key=str(g), num=num, title=title, pages=[], chapter=None,
                             needs=[], subs=[], state="extra", labels=[], decls=[])
        key = f"{d['path']}::{d['token']}"
        mine = issues.get(key, [])
        if mine:
            matched.add(key)
        if keys[key] > 1 and mine:
            note(notes, f"{key} names {keys[key]} declarations; their proof issue cannot be told apart.")
        open_issue = next((i for i in mine if i["open"]), None)
        issue = open_issue or (max(mine, key=lambda i: i["number"]) if mine else None)
        if d["kind"] != "theorem":
            state = "def"
        elif not d["sorry"]:
            state = "proved"
            if open_issue:
                note(notes, f"#{open_issue['number']} is still open although `{d['show']}` has no "
                            "sorry at this commit; `scripts/issues.py --apply` will close it.")
        elif open_issue and open_issue["claimed"]:
            state = "claimed"
        elif open_issue:
            state = "open"
        else:
            state = "unfiled"
        paper = paper_item(d["doc"])
        d.update(group=g, state=state, issue=issue["number"] if issue else None,
                 who=issue["who"] if issue and state == "claimed" else [], paper=paper)
        index[n] = len(decls)
        decls.append(d)
        groups[g]["decls"].append(n)

    unfiled = [d["show"] for d in decls if d["state"] == "unfiled"]
    if unfiled:
        note(notes, (f"{len(unfiled)} theorems have" if len(unfiled) > 1 else "1 theorem has")
                    + " a sorry but no open proof issue yet (`scripts/issues.py --apply` opens them): "
                    + ", ".join(f"`{n}`" for n in unfiled[:12]) + (" …" if len(unfiled) > 12 else "") + ".")
    for key, lst in issues.items():
        if key not in matched:
            for i in lst:
                if i["open"]:
                    note(notes, f"#{i['number']} is open for `{key.split('::')[-1]}`, which is not in "
                                f"{key.split('::')[0]} at this commit (renamed, moved or removed).")

    # Items: declarations grouped by the paper item their docstring cites.
    out_groups = []
    for g, grp in groups.items():
        names = grp["decls"]
        items, item_of = group_items(names, lib, by_file=not isinstance(g, int))

        # Bands: the paper's subsections, in paper order.
        sub_titles = collections.OrderedDict((a, b) for a, b in grp.get("subs", []))
        bands, band_of_item, prev_band = collections.OrderedDict(), {}, None
        for s in sub_titles:
            bands[s] = []
        for k, it in items.items():
            comps = it["number"].split(".") if it["number"] else []
            band = None
            for depth in (3, 2):
                cand = ".".join(comps[:depth])
                if len(comps) >= depth and cand in sub_titles:
                    band = cand
                    break
            if band is None and not sub_titles and len(comps) >= 3:
                band = ".".join(comps[:3])
            if band is None:
                band = prev_band if prev_band is not None else (next(iter(bands), None) or "")
            bands.setdefault(band, []).append(k)
            band_of_item[k] = band
            prev_band = band
        item_keys = [k for b in bands.values() for k in b]
        item_index = {k: i for i, k in enumerate(item_keys)}

        # Item edges inside the group, from the declaration dependencies.
        stmt_e, any_e = collections.defaultdict(set), collections.defaultdict(set)
        for n in names:
            d = lib.user[n]
            a = item_index[item_of[n]]
            for kind, deps in (("stmt", d["stmt"]), ("proof", d["proof"])):
                for dep in deps:
                    if dep in item_of and item_index[item_of[dep]] != a:
                        b = item_index[item_of[dep]]
                        any_e[a].add(b)
                        if kind == "stmt":
                            stmt_e[a].add(b)
        # Grouping can close a cycle between two items; drop the back edges so that the
        # reduction below works on a DAG (they are still listed per declaration).
        dag = {a: {b for b in bs if b < a} for a, bs in any_e.items()}
        edges = [[a, b, 0 if b in stmt_e[a] else 1]
                 for a, b in transitive_reduction(range(len(item_keys)), dag)]

        g_decls = [index[n] for n in names]
        thms = [lib.user[n] for n in names if lib.user[n]["kind"] == "theorem"]
        counts = collections.Counter(d["state"] for d in thms)
        out_items = []
        for k in item_keys:
            it = items[k]
            out_items.append(dict(key=k, label=it["label"], page=it["page"], band=band_of_item[k],
                                  decls=[index[n] for n in it["decls"]]))
        uses = collections.Counter()
        for n in names:
            d = lib.user[n]
            for dep in d["stmt"] + d["proof"]:
                og = lib.user[dep]["group"]
                if og != g:
                    uses[og] += 1
        g_files = sorted({lib.user[n]["path"] for n in names},
                         key=lambda p: min(lib.user[n]["mi"] for n in names if lib.user[n]["path"] == p))
        out_groups.append(dict(
            key=grp["key"], id=grp["id"], num=grp["num"], title=grp["title"], pages=grp["pages"],
            chapter=grp["chapter"], state=grp["state"], needs=[n for n in grp["needs"] if n in by_id],
            lane=grp.get("lane"), row=grp.get("row"),
            defs=len(names) - len(thms), thms=len(thms),
            proved=counts["proved"], claimed=counts["claimed"], open=counts["open"],
            unfiled=counts["unfiled"],
            solid=sum(1 for d in thms if d["state"] == "proved" and not d["open_below"]
                      and not d["hidden_sorry"]),
            files=g_files, items=out_items,
            bands=[[b, sub_titles.get(b, "")] for b, ks in bands.items() if ks],
            edges=edges, uses=sorted(([groups[og]["key"], c] for og, c in uses.items()),
                                     key=lambda x: -x[1]),
            _decls=g_decls))

    # Overview layout.
    lanes = sorted({s["chapter"] for s in sections}, key=chapter_sort)
    layout_sections(sections, lanes)
    for og in out_groups:
        if og["id"] is not None:
            og["lane"], og["row"] = by_id[og["id"]]["lane"], by_id[og["id"]]["row"]
    need_deps = {s["id"]: {n for n in s["needs"] if n in by_id} for s in sections}
    drawn = collections.defaultdict(list)
    try:
        for a, b in transitive_reduction(sorted(by_id), need_deps):
            drawn[a].append(b)
    except RecursionError:
        drawn = {a: sorted(bs) for a, bs in need_deps.items()}
    for og in out_groups:
        og["needsDrawn"] = sorted(drawn.get(og["id"], [])) if og["id"] is not None else []

    for s in sections:
        if s["state"] == "blocked" and all(by_id[n]["state"] == "stated" for n in s["needs"] if n in by_id):
            note(notes, f"#{s['id']} ({s['num']}) is labelled blocked, but everything it needs is closed; "
                        "`scripts/issues.py --apply` will unblock it.")
        if s["state"] == "ready" and any(
                by_id[n]["state"] != "stated" for n in s["needs"] if n in by_id):
            note(notes, f"#{s['id']} ({s['num']}) is not labelled blocked although it needs a section "
                        "that is still open.")
        missing = [n for n in s["needs"] if n not in by_id]
        if missing:
            note(notes, f"#{s['id']} needs {', '.join('#%d' % n for n in missing)}, which "
                        "is not a section issue.")
        g = next(og for og in out_groups if og["id"] == s["id"])
        if s["state"] == "stated" and not g["_decls"]:
            note(notes, f"#{s['id']} ({s['num']}) is closed but no declarations were found for it.")
        if s["state"] == "blocked" and g["_decls"]:
            note(notes, f"#{s['id']} ({s['num']}) is labelled blocked but already has "
                        f"{len(g['_decls'])} declarations on main.")
        if s["state"] == "ready" and g["_decls"]:
            note(notes, f"#{s['id']} ({s['num']}) is open and unclaimed with {len(g['_decls'])} "
                        "declarations on main: digested in part, the rest is free to take.")

    # Declarations, compact: dependencies as indices.
    file_list = sorted({d["path"] for d in decls})
    file_idx = {p: i for i, p in enumerate(file_list)}
    group_idx = {og["key"]: i for i, og in enumerate(out_groups)}
    kind_code = {"theorem": "t", "def": "d", "abbrev": "a", "structure": "s", "class": "c",
                 "inductive": "i", "instance": "n", "opaque": "o", "axiom": "x"}
    out_decls = []
    for d in decls:
        p = d["paper"]
        flags = (1 if d["private"] else 0) | (2 if "Deviation:" in d["doc"] else 0) \
            | (4 if d["hidden_sorry"] else 0) | (0 if p else 8)
        out_decls.append([
            d["show"], kind_code.get(d["kind"], "d"), d["state"],
            group_idx[groups[d["group"]]["key"]], file_idx[d["path"]], d["line"],
            d["issue"], p["page"] if p else None, p["raw"] if p else "",
            excerpt(p["text"] if p else d["doc"]), flags, d["open_below"],
            [index[x] for x in d["stmt"]], [index[x] for x in d["proof"]], d["who"]])
        if d["kind"] in ("axiom", "opaque"):
            note(notes, f"`{d['show']}` is an {d['kind']}, which AGENTS.md forbids.")
    for og in out_groups:
        del og["_decls"]

    # Waves: only the chapters that have no section issue yet.
    seeded = set()
    for i in section_issues:
        for a, b in re.findall(r"§\s*([A-E]|\d+)\.(\d+)", i["title"]):
            seeded.add(f"{a}.{b}")
    out_waves = []
    for w in waves:
        todo = [p for p in (wave_part(c, seeded, toc_chapters, toc_sections) for c in w["chapters"]) if p]
        if w["chapters"] and not todo:
            continue
        whole = sum(len(c["nums"]) for c in w["chapters"])
        out_waves.append(dict(name=w["name"], text=w["text"], status=w["status"], chapters=todo,
                              partial=sum(c["sections"] for c in todo) != whole))

    # Vendored third-party Lean (External/) is shown on the map but is not the project's work, so
    # the totals leave it out.
    own = [d for d in decls if d["group"] != "external"]
    thms = [d for d in own if d["kind"] == "theorem"]
    st = collections.Counter(d["state"] for d in thms)
    sec_states = collections.Counter(s["state"] for s in sections)
    totals = dict(
        defs=len(own) - len(thms), thms=len(thms), proved=st["proved"],
        solid=sum(1 for d in thms if d["state"] == "proved" and not d["open_below"]
                  and not d["hidden_sorry"]),
        open=st["open"] + st["claimed"] + st["unfiled"], claimed=st["claimed"], unfiled=st["unfiled"],
        paper=sum(1 for d in thms if d["paper"]),
        paperProved=sum(1 for d in thms if d["paper"] and d["state"] == "proved"),
        sections=len(sections), stated=sec_states["stated"], digesting=sec_states["digesting"],
        ready=sec_states["ready"], blocked=sec_states["blocked"],
        issuesOpen=sum(1 for i in proof_issues if i["state"] == "OPEN"),
        issuesClosed=sum(1 for i in proof_issues if i["state"] != "OPEN"))

    stamp = lambda s: int(datetime.datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp())
    timeline = dict(
        filed=sorted(stamp(i["createdAt"]) for i in proof_issues if i.get("createdAt")),
        closed=sorted(stamp(i["closedAt"]) for i in proof_issues
                      if i.get("closedAt") and i["state"] != "OPEN"))

    subject = run(["git", "log", "-1", "--format=%s", head], check=False).stdout.strip()
    dirty = bool(run(["git", "--no-optional-locks", "status", "--porcelain", "--", LIB],
                     check=False).stdout.strip())
    if dirty:
        note(notes, "The checkout has uncommitted changes under RiemannMasullo/; source links point "
                    "at the commit and may be a few lines off.")
    meta = dict(
        generated=datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        commit=head, subject=subject, repo=repo["url"], name=repo["nameWithOwner"],
        status=readme_status, sorrySource="build" if warnings is not None else "terms",
        pagesTotal=max((c["end"] for c in toc_chapters.values()), default=0))
    chapters = [dict(key=k, label=chapter_label(k) if k != "other" else "Other",
                     title=toc_chapters.get(k, {}).get("title", "")) for k in lanes]
    errata = errata_model(out_groups, out_decls, notes)
    return dict(meta=meta, totals=totals, timeline=timeline, chapters=chapters, groups=out_groups,
                waves=out_waves, files=file_list, decls=out_decls, notes=notes, errata=errata)


ERRATA_ROW = re.compile(r"^\|\s*([FIMR]\d+)\s*\|")


def errata_model(groups, decls, notes):
    """The problems listed in ERRATA.md, each placed in the section its page falls in.

    Entries: [id, kind, checked, page, where, summary, group index or -1, [declaration indices
    of the `Printed.…` statements it names], no repair known]. Withdrawn and moved rows are
    left out. Gaps: the table of places where no repair is known."""
    path = ROOT / "ERRATA.md"
    if not path.exists():
        return None
    text = path.read_text(encoding="utf-8")
    by_name = {d[0]: i for i, d in enumerate(decls)}
    spans = [(i, g["pages"]) for i, g in enumerate(groups) if g["id"] is not None and g["pages"]]
    # The numbers a section covers: those in its title (§5.2, §C.2.1–C.2.3) and its subsections.
    prefixes = {i: [n for n in re.findall(NUMBER.pattern, g["num"])] + [b[0] for b in g.get("bands", [])]
                for i, g in enumerate(groups)}

    def group_of(page, where=""):
        if page is None:
            return -1
        hits = [(sum(b - a + 1 for a, b in pp), i) for i, pp in spans
                if any(a <= page <= b for a, b in pp)]
        if len(hits) > 1:
            # Sections share their first and last pages: prefer the one the item's number is in.
            item = NUMBER.search(where)
            named = [h for h in hits if item and any(
                item.group(0) == n or item.group(0).startswith(n + ".") for n in prefixes[h[1]])]
            hits = named or hits
        return min(hits)[1] if hits else -1

    def first_page(s):
        m = re.search(r"\bpp?\.\s*(\d+)", s)
        return int(m.group(1)) if m else None

    clean = lambda s: excerpt(re.sub(r"\*\*|`", "", s), 240)
    # A cell may contain a bar written `\|` (absolute values, norms): split only at the others.
    cells_of = lambda line: [c.strip().replace("\\|", "|")
                             for c in re.split(r"(?<!\\)\|", line.strip().strip("|"))]
    entries, gaps, no_repair = [], [], set()
    for part in re.split(r"^## ", text, flags=re.M)[1:]:
        title, _, body = part.partition("\n")
        if title.startswith("Where no repair is known"):
            for line in body.splitlines():
                c = cells_of(line)
                if not line.startswith("| ") or len(c) < 4 or c[0] in ("Item", "") or set(c[0]) <= set("-: "):
                    continue
                ids = re.findall(r"\b[FIMR]\d+\b", c[1])
                no_repair.update(ids)
                page = first_page(c[0])
                gaps.append(dict(item=clean(c[0]), ids=ids, missing=clean(c[2]), later=c[-1],
                                 page=page, group=group_of(page, c[0])))
            continue
        for line in body.splitlines():
            if not ERRATA_ROW.match(line):
                continue
            c = cells_of(line)
            eid, where, checked = c[0], c[1], c[-1]
            if checked in ("withdrawn", "moved") or len(c) < 5:
                continue
            kind = eid[0]
            lean = c[-3] if kind in "FI" and len(c) >= 6 else ""
            names = re.findall(r"`(Printed\.[\w.'₀-₉]+)`", lean)
            refs = [by_name[n] for n in names if n in by_name]
            page = first_page(where)
            entries.append([eid, kind, checked, page, clean(where), clean(c[2]), group_of(page, where),
                            refs, False])
    for e in entries:
        e[8] = e[0] in no_repair
    if not entries:
        note(notes, "ERRATA.md has no rows the page could read; the problems view is empty.")
    return dict(entries=entries, gaps=gaps)


def validate(model):
    """Refuse to publish a page whose numbers do not add up."""
    decls, groups, t = model["decls"], model["groups"], model["totals"]
    seen = [i for g in groups for it in g["items"] for i in it["decls"]]
    counted = [g for g in groups if g["key"] != "external"]       # the totals leave External out
    checks = [
        (sorted(seen) == list(range(len(decls))), "every declaration sits in exactly one item"),
        (t["proved"] + t["open"] == t["thms"], "proved + open = theorems"),
        (sum(g["thms"] for g in counted) == t["thms"], "section theorem counts add up"),
        (sum(g["proved"] for g in counted) == t["proved"], "section proved counts add up"),
        (sum(g["defs"] for g in counted) == t["defs"], "section definition counts add up"),
        (all(0 <= j < len(decls) and j != i for i, d in enumerate(decls) for j in d[12] + d[13]),
         "dependencies point at declarations"),
        (all(0 <= a < len(g["items"]) and 0 <= b < len(g["items"]) for g in groups for a, b, _ in g["edges"]),
         "item edges point at items"),
        (len({g["key"] for g in groups}) == len(groups), "section keys are unique"),
        (len({(g["lane"], g["row"]) for g in groups if g["id"] is not None})
         == sum(1 for g in groups if g["id"] is not None), "no two sections share a cell"),
    ]
    bad = [what for ok, what in checks if not ok]
    if bad:
        raise RuntimeError("the page data is inconsistent: " + "; ".join(bad))


# ---------------------------------------------------------------------------------------------
# History and output


def update_history(path, model):
    """Append one line of totals unless nothing changed; return (history, previous snapshot)."""
    history = []
    if path.exists():
        for line in path.read_text(encoding="utf-8").splitlines():
            try:
                history.append(json.loads(line))
            except ValueError:
                pass
    t = model["totals"]
    snap = dict(time=model["meta"]["generated"], commit=model["meta"]["commit"][:10],
                stated=t["thms"], proved=t["proved"], open=t["open"], claimed=t["claimed"],
                defs=t["defs"], sections_closed=t["stated"], sections=t["sections"])
    same = lambda a, b: all(a.get(k) == b.get(k) for k in snap if k != "time")
    if not history or not same(history[-1], snap):
        with open(path, "a", encoding="utf-8") as fh:
            fh.write(json.dumps(snap) + "\n")
        history.append(snap)
    prev = history[-2] if len(history) > 1 else None
    return history, prev


def render(model):
    template = (HERE / "template.html").read_text(encoding="utf-8")
    blob = json.dumps(model, ensure_ascii=False, separators=(",", ":"))
    # Inside <script>: keep `</script>` and `<!--` from ending or confusing the block.
    blob = blob.replace("<", "\\u003c").replace("\u2028", "\\u2028").replace("\u2029", "\\u2029")
    if "/*__DATA__*/null" not in template:
        raise RuntimeError("template.html has no /*__DATA__*/null placeholder")
    return template.replace("/*__DATA__*/null", blob)


def collect(args):
    head = git_head()
    files = module_files()
    warnings = None if args.no_build else lake_build()
    files_after = module_files()
    if files_after != files:
        raise Retry("source files appeared or disappeared during the build")
    rows = lean_constants(sorted(files))
    repo, section_issues, proof_issues = fetch_issues()
    model = build_model(repo, section_issues, proof_issues, rows, files, warnings, head)
    model["merged"] = fetch_contributions(repo)
    if git_head() != head:
        raise Retry("HEAD moved during the run")
    return model


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", default=str(ROOT / ".agent" / "progress" / "index.html"))
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--stats", action="store_true")
    args = ap.parse_args()
    model = None
    for attempt in range(6):
        try:
            model = collect(args)
            break
        except Retry as why:
            print(f"retrying ({attempt + 1}/6): {str(why).splitlines()[0]}", file=sys.stderr)
            last = str(why)
            time.sleep(5 + 5 * attempt)
    if model is None:
        sys.exit("gave up; the existing page was left alone.\n" + last)
    validate(model)

    out = pathlib.Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    history, prev = update_history(out.parent / "history.jsonl", model)
    model["prev"] = prev
    model["history"] = history[-400:]
    html = render(model)
    fd, tmp = tempfile.mkstemp(dir=out.parent, suffix=".tmp")
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        fh.write(html)
    os.chmod(tmp, 0o644)
    os.replace(tmp, out)

    t, m = model["totals"], model["meta"]
    print(f"{out}  ({len(html) // 1024} KB)")
    print(f"commit {m['commit'][:10]}  sections {t['stated']}/{t['sections']} stated "
          f"({t['digesting']} being digested, {t['ready']} ready, {t['blocked']} blocked)")
    print(f"definitions {t['defs']}  theorems {t['thms']}: proved {t['proved']} "
          f"({t['solid']} resting on no sorry), open {t['open']} "
          f"({t['claimed']} claimed, {t['unfiled']} without an issue)")
    print(f"proof issues: {t['issuesOpen']} open, {t['issuesClosed']} closed")
    if args.stats:
        for g in model["groups"]:
            print(f"  {g['key']:<12} {g['state']:<9} {g['num']:<16} defs {g['defs']:>3}  thms {g['thms']:>3}"
                  f"  proved {g['proved']:>3}  items {len(g['items']):>3}  edges {len(g['edges']):>3}")
    if model["notes"]:
        print(f"{len(model['notes'])} notes:")
        for n in model["notes"]:
            print("  - " + n)


if __name__ == "__main__":
    main()
