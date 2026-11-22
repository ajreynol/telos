"""Shared source inventory for the LOC and runtime dependency reports."""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
LOGOS = ROOT / ".lake/packages/Cpc"

# Keep the specification in sync with TRUSTED.md and check-hygiene.sh.
SPEC = {
    "Telos/Core/Node/Kind.lean",
    "Telos/Core/Node/TypeNode.lean",
    "Telos/Core/Node/SkolemId.lean",
    "Telos/Core/Node/Node.lean",
    "Telos/Core/Node/ToEo.lean",
    "verification/TelosProofs/Core/Spec.lean",
}
TCB = SPEC | {"Telos/Core/Profile.lean"}
CHAR_RE = re.compile(r"'(?:\\[^\n]|[^'\\\n])'")
RAW_STRING_RE = re.compile(r'r(#+)?"')


def lean_files(base: Path):
    for path in sorted(base.rglob("*.lean")):
        if not {".lake", ".git"}.intersection(path.relative_to(base).parts):
            yield path


def mask_comments(text: str, *, strings: bool = False) -> str:
    """Mask nested comments, preserving positions and respecting quoted strings.

    Optionally mask string contents too, for scanning imports and commands.
    Quotes remain so lines containing only a string still count as LOC.
    """
    out = list(text)
    i, depth = 0, 0
    while i < len(text):
        start = i
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif char := CHAR_RE.match(text, i):
            i = char.end()
            continue
        elif raw := RAW_STRING_RE.match(text, i):
            terminator = '"' + (raw[1] or "")
            end = text.find(terminator, raw.end())
            i = len(text) if end == -1 else end + len(terminator)
            if strings:
                for j in range(raw.end(), len(text) if end == -1 else end):
                    if text[j] != "\n":
                        out[j] = " "
            continue
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i = min(i + 2, len(text))
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            if strings:
                for j in range(start + 1, i - 1):
                    if text[j] != "\n":
                        out[j] = " "
            continue
        else:
            i += 1
            continue
        for j in range(start, i):
            if text[j] != "\n":
                out[j] = " "
    return "".join(out)


def count_loc(path: Path) -> int:
    return sum(bool(line.strip()) for line in mask_comments(path.read_text()).splitlines())


def category_of(rel: str) -> str | None:
    if rel in TCB:
        return "spec"
    if rel.startswith(("verification/TelosProofs/", "verification/TelosFull/")):
        return "proofs"
    if rel.startswith(("TelosTests/", "scripts/")) or rel == "FuzzMain.lean":
        return "support"
    if rel.startswith("Telos/") or rel in {"Telos.lean", "Main.lean"}:
        return "solver"
    return None


def module_path(module: str) -> str:
    prefix = "verification/" if module.startswith(("TelosProofs.", "TelosFull.")) else ""
    return prefix + module.replace(".", "/") + ".lean"


IMPORT_RE = re.compile(r"^[ \t]*(?:public\s+|meta\s+)*import\s+(?:all\s+)?([^\n]+)", re.M)


def imports(path: Path) -> list[str]:
    text = mask_comments(path.read_text(), strings=True)
    return [name for match in IMPORT_RE.finditer(text) for name in match[1].split()]


def logos_spec_modules() -> set[str]:
    """The pinned specification's import closure (not the CPC checker)."""
    seen: set[str] = set()
    stack = ["Cpc.Spec", "Cpc.SmtTranslate"]
    while stack:
        module = stack.pop()
        if module in seen or not module.startswith(("Cpc.", "Logos.")):
            continue
        path = LOGOS / module_path(module)
        if not path.is_file():
            raise FileNotFoundError(f"missing Logos module {path}; run `lake build`")
        seen.add(module)
        stack.extend(imports(path))
    return seen


# A source LOC convention, not executable-code analysis. Inline proof terms
# (including termination proofs) stay with their definitions.
COMMAND_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?:@\[[^\n]*?\][ \t]*)*"
    r"(?:(?:private|protected|public|noncomputable|unsafe|partial|nonrec)[ \t]+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|opaque|instance|inductive|structure|class|"
    r"namespace|section|end|mutual|open|variable|universe|attribute|export|"
    r"initialize|builtin_initialize|syntax|macro|elab|set_option|include|omit|"
    r"deriving|example|import)\b|^(?P<hashindent>[ \t]*)#[a-zA-Z_]+", re.M,
)


def inline_proof_lines(text: str) -> set[int]:
    """Zero-based lines occupied by standalone theorem/lemma commands."""
    masked = mask_comments(text, strings=True)
    commands = list(COMMAND_RE.finditer(masked))
    lines = masked.splitlines()

    def first_line(command):
        line = masked.count("\n", 0, command.start())
        indent = len(command["indent"] or command["hashindent"] or "")
        while line:
            previous = lines[line - 1]
            if not previous.strip():
                line -= 1
            elif (previous.strip().startswith("@[") and previous.strip().endswith("]")
                  and len(previous) - len(previous.lstrip()) <= indent):
                line -= 1
            else:
                break
        return line

    result: set[int] = set()
    for i, command in enumerate(commands):
        if command["kind"] not in {"theorem", "lemma"}:
            continue
        indent = len(command["indent"])
        last = len(lines)
        for following in commands[i + 1:]:
            if len(following["indent"] or following["hashindent"] or "") <= indent:
                last = first_line(following)
                break
        result.update(range(first_line(command), last))
    return result
