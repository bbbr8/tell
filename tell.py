import sys, re, json, os, hashlib, datetime
from pathlib import Path
from decimal import Decimal
from fractions import Fraction

VERSION = "3.1.0"
TRUE, OPEN = 2, 1
TRUTH_NAME = {2: "TRUE", 1: "OPEN"}
META_PREDS = ("premise_of", "atom_tier", "tier_below")


def die(msg, code=2):
    sys.stderr.write("tell: " + msg + "\n")
    sys.exit(code)


# ---------------------------------------------------------------- terms
VAR = re.compile(r"^[A-Z][A-Za-z0-9_]*$")
NUM = re.compile(r"^[+-]?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?$")
RATIONAL = re.compile(r"^[+-]?\d+/[1-9]\d*$")
DATE = re.compile(r"^\d{4}-\d{2}-\d{2}$")


class Date(Fraction):
    """A date is a number of days (proleptic ordinal) that prints as ISO."""
    def __new__(cls, iso):
        d = datetime.date.fromisoformat(iso)
        o = Fraction.__new__(cls, d.toordinal())
        o.iso = iso
        return o

    @classmethod
    def from_ordinal(cls, n):
        return cls(datetime.date.fromordinal(int(round(n))).isoformat())

    def __str__(self):
        return self.iso
    __repr__ = __str__

    def __eq__(self, other):
        return isinstance(other, Date) and Fraction.__eq__(self, other)

    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(("tell.date", self.numerator))

    def __deepcopy__(self, memo):
        result = Date(self.iso)
        memo[id(self)] = result
        return result


_anon = [0]
TIER_SYMBOLS = set()


class Variable(str):
    """Variables retain their identity when another Program is subsequently loaded."""


class Quoted(str):
    """A quoted constant may contain spaces, punctuation, or uppercase letters."""


def parse_term(tok):
    tok = tok.strip()
    if tok == "_":
        _anon[0] += 1
        return Variable("_G%d" % _anon[0])
    if tok.startswith('"'):
        try:
            value = json.loads(tok)
        except (ValueError, TypeError):
            die(f"invalid quoted term {tok!r}")
        if not isinstance(value, str):
            die("a quoted term must be a string")
        return Quoted(value)
    if DATE.match(tok):
        try: return Date(tok)
        except ValueError as error: die(f"invalid date {tok!r}: {error}")
    if NUM.match(tok) or RATIONAL.match(tok):
        return Fraction(tok)
    if tok not in TIER_SYMBOLS and VAR.fullmatch(tok):
        return Variable(tok)
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", tok):
        die(f"invalid term {tok!r}; use double quotes for text")
    return tok


def is_var(t):
    return isinstance(t, Variable)


ATOM = re.compile(r"^([a-z][A-Za-z0-9_]*)\s*(?:\(([^()]*)\))?$")
AGG = re.compile(r"^([A-Z][A-Za-z0-9_]*)\s*=\s*(count_distinct|count|sum|min|max|avg)\((.+)\)$")
GTOK = re.compile(r'\d{4}-\d{2}-\d{2}|\d+(?:\.\d+)?(?:[eE][+-]?\d+)?|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z0-9_]*|>=|<=|==|!=|>|<|=|[()*/+-]')
CMP = {">=", "<=", "==", "!=", ">", "<"}


def split_top(s):
    """Split on commas outside parentheses and JSON strings."""
    out, depth, cur, quoted, escaped = [], 0, [], False, False
    for ch in s:
        if quoted:
            if ch == "\n": die("use a JSON escape for a newline inside a quoted term")
            cur.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                quoted = False
            continue
        if ch == '"':
            quoted = True
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth < 0:
                die("unexpected ')' while parsing arguments")
        if ch == "," and depth == 0:
            out.append("".join(cur)); cur = []
        else:
            cur.append(ch)
    if "".join(cur).strip():
        out.append("".join(cur))
    elif s.rstrip().endswith(","):
        die("trailing comma requires another term or body item")
    if quoted or depth:
        die("unterminated string or parentheses")
    return [x.strip() for x in out]


def unquoted(s):
    """Mask strings without changing offsets, for statement-level annotations."""
    out, quoted, escaped = [], False, False
    for ch in s:
        if quoted:
            out.append(" ")
            if escaped: escaped = False
            elif ch == "\\": escaped = True
            elif ch == '"': quoted = False
        elif ch == '"': quoted = True; out.append(" ")
        else: out.append(ch)
    return "".join(out)


def json_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result: raise ValueError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def finite_json(value):
    raise ValueError("non-finite JSON number " + value)


def parse_atom(s):
    m = re.fullmatch(r"([a-z][A-Za-z0-9_]*)\s*(?:\((.*)\))?", s.strip(), re.S)
    if not m:
        return None
    args = []
    if m.group(2) is not None and m.group(2).strip():
        args = [parse_term(a) for a in split_top(m.group(2))]
    return (m.group(1), tuple(args))


def parse_guard(s):
    toks, pos = [], 0
    while pos < len(s):
        if s[pos].isspace():
            pos += 1
            continue
        m = GTOK.match(s, pos)
        if m is None:
            return None
        toks.append(m.group()); pos = m.end()
    depth, comparisons = 0, []
    for i, tok in enumerate(toks):
        if tok == "(": depth += 1
        elif tok == ")": depth -= 1
        elif depth == 0 and tok in CMP | {"="}: comparisons.append(i)
    if not comparisons:
        return None
    if len(comparisons) != 1:
        die("an expression needs exactly one comparison or binding operator")
    i = comparisons[0]; op = toks[i]
    left, right = expression(toks[:i]), expression(toks[i+1:])
    if op == "=":
        if left[0] != "value" or not is_var(left[1]):
            die("the left side of a binding must be a variable")
        return "bind", (left[1], right)
    return "guard", (left, op, right)


def expression(tokens):
    """Parse a restricted arithmetic tree; no Python eval or arbitrary calls."""
    index = 0
    def part(min_precedence=0):
        nonlocal index
        if index >= len(tokens): die("incomplete arithmetic expression")
        tok = tokens[index]; index += 1
        if tok in ("+", "-"):
            node = ("unary", tok, part(30))
        elif tok == "(":
            node = part()
            if index >= len(tokens) or tokens[index] != ")": die("missing ')' in expression")
            index += 1
        elif tok in CMP | {"=", ")", "*", "/"}:
            die(f"unexpected {tok!r} in expression")
        else:
            node = ("value", parse_term(tok))
        while index < len(tokens):
            op = tokens[index]
            precedence = {"+": 10, "-": 10, "*": 20, "/": 20}.get(op, -1)
            if precedence < min_precedence: break
            index += 1
            node = ("binary", op, node, part(precedence + 1))
        return node
    node = part()
    if index != len(tokens): die(f"unexpected token {tokens[index]!r} in expression")
    return node


def expr_vars(node):
    if node[0] == "value": return {node[1]} if is_var(node[1]) else set()
    if node[0] == "unary": return expr_vars(node[2])
    return expr_vars(node[2]) | expr_vars(node[3])


def expression_text(text):
    tokens, pos = [], 0
    while pos < len(text):
        if text[pos].isspace():
            pos += 1
            continue
        match = GTOK.match(text, pos)
        if match is None:
            die(f"invalid aggregate expression near {text[pos:]!r}")
        tokens.append(match.group()); pos = match.end()
    return expression(tokens)


def fmt_expr(node):
    if node[0] == "value": return fmt_val(node[1])
    if node[0] == "unary": return node[1] + fmt_expr(node[2])
    return "(" + fmt_expr(node[2]) + " " + node[1] + " " + fmt_expr(node[3]) + ")"


def statements(text, fname, with_spans=False):
    """Period-terminated statements, with quote-aware comments and decimals."""
    buf, depth, quoted, escaped, comment = [], 0, False, False, False
    line = first = 1
    start = 0
    for i, ch in enumerate(text):
        if comment:
            if ch == "\n":
                comment = False; line += 1
                if buf: buf.append(" ")
            continue
        if not buf and not ch.isspace(): first = line; start = i
        if quoted:
            if ch == "\n": die(f"{fname}:{line}: use a JSON escape for a newline inside a quoted term")
            buf.append(ch)
            if escaped: escaped = False
            elif ch == "\\": escaped = True
            elif ch == '"': quoted = False
        elif ch == "%": comment = True
        elif ch == '"': quoted = True; buf.append(ch)
        elif ch == "(": depth += 1; buf.append(ch)
        elif ch == ")":
            depth -= 1
            if depth < 0: die(f"{fname}:{line}: unexpected ')'")
            buf.append(ch)
        elif ch == "." and depth == 0 and not (i and text[i-1].isdigit() and i+1 < len(text) and text[i+1].isdigit()):
            value = "".join(buf).strip(); buf = []
            if value: yield (first, value, start, i+1) if with_spans else (first, value)
        else:
            if buf or not ch.isspace(): buf.append(" " if ch == "\n" else ch)
        if ch == "\n": line += 1
    if quoted or depth: die(f"{fname}:{first}: unterminated string or parentheses")
    if "".join(buf).strip(): die(f"{fname}:{first}: statement must end with '.'")


def parse_body(text, ln, allow_agg=True):
    body = []
    for part in split_top(text):
        m = AGG.match(part)
        if m:
            inner = split_top(m.group(3))
            if len(inner) != (1 if m.group(2) == "count" else 2):
                die(f"line {ln}: {m.group(2)} needs an atom" + (" only" if m.group(2) == "count" else " and one expression"))
            atom = parse_atom(inner[0])
            if not atom:
                die(f"line {ln}: bad aggregate atom '{inner[0]}'")
            over = inner[1] if len(inner) > 1 else None
            if m.group(2) != "count" and not over:
                die(f"line {ln}: {m.group(2)} needs a variable to aggregate over")
            if m.group(2) == "count" and over:
                die(f"line {ln}: count takes no aggregation variable")
            if over: expression_text(over)
            body.append(("agg", (m.group(1), m.group(2), atom, over)))
            continue
        if part.startswith("not "):
            a = parse_atom(part[4:])
            if not a:
                die(f"line {ln}: bad negated atom '{part}'")
            body.append(("not", a))
            continue
        g = parse_guard(part)
        a = parse_atom(part)
        if a and not g:
            body.append(("atom", a))
        elif g:
            body.append(g)
        else:
            die(f"line {ln}: cannot parse body item '{part}'")
    return body


# ---------------------------------------------------------------- program
class Program:
    def __init__(self):
        self.tiers = ["F0", "F1", "sworn", "native", "derived", "synthetic"]
        self.explicit_tiers = False
        self.anchors = {}          # name → dict(text, file, sha256, used)
        self.facts = {}            # (pred, args) → dict(truth, tier, anchors, prov)
        self.rules = []            # dict(name, head, body, fired)
        self.forbids = []          # dict(name, body)
        self.defeats = []          # dict(name, target, body)
        self.closed = {}           # pred → dict(text, anchors, tier)
        self.shows = []
        self.base_dir = "."
        self.source_files = []
        self._json_cache = {}
        self._read_sources = {}
        self.lines = []            # (file, ln, raw) for lint/verify --pin
        self.include_stack = []
        self.limits = {"max_facts": 20000, "max_rounds": 1000, "max_bindings": 50000}
        self.rounds = 0

    def tier_rank(self, t):
        if t not in self.tiers:
            die(f"undeclared tier '{t}' — declare it in `tier order:`")
        return self.tiers.index(t)

    def weakest(self, ts):
        return max(ts, key=self.tier_rank) if ts else "derived"

    def stronger(self, a, b):
        return self.tier_rank(a) < self.tier_rank(b)

    # -- extern facts
    def json_at(self, anchor, path, ln):
        a = self.anchors.get(anchor)
        if a is None:
            die(f"line {ln}: unknown anchor @{anchor}")
        if not a.get("file"):
            die(f"line {ln}: anchor {anchor} has no `file` — `from` needs one")
        fp = os.path.join(a.get("dir", self.base_dir), a["file"])
        if fp not in self._json_cache:
            if not os.path.exists(fp):
                die(f"line {ln}: anchor file missing: {fp}")
            with open(fp, "rb") as source_file:
                source_bytes = source_file.read()
            try:
                self._json_cache[fp] = json.loads(source_bytes, parse_float=Decimal, object_pairs_hook=json_object, parse_constant=finite_json)
            except (ValueError, UnicodeError) as error:
                die(f"line {ln}: invalid JSON in {a['file']}: {error}")
            self._read_sources[fp] = hashlib.sha256(source_bytes).hexdigest()
        node = self._json_cache[fp]
        if not path.startswith("$"):
            die(f"line {ln}: path must start with $")
        steps = re.findall(r"\.([^.\[\]]+)|\[(\d+)\]", path[1:])
        if "".join("." + k if k else "[" + i + "]" for k, i in steps) != path[1:]:
            die(f"line {ln}: invalid scalar JSON path {path!r}")
        for step in steps:
            key, idx = step
            try:
                node = node[int(idx)] if idx else node[key]
            except (KeyError, IndexError, TypeError):
                die(f"line {ln}: path {path} not found in {a['file']}")
        if isinstance(node, bool):
            node = "true" if node else "false"
        if not isinstance(node, (int, float, Decimal, Fraction, str)):
            die(f"line {ln}: path {path} is not a scalar")
        return node, a["file"]


def _symbolize(v):
    if isinstance(v, (int, float, Decimal, Fraction)):
        return Fraction(str(v))
    if isinstance(v, str) and DATE.match(v.strip()):
        return Date(v.strip())
    s = re.sub(r"[^A-Za-z0-9_]", "_", str(v)).lower()
    return s if s and s[0].isalpha() else "v_" + s


def parse_into(p, text, fname):
    canonical = os.path.realpath(fname) if fname != "<string>" else fname
    if canonical in p.include_stack:
        die("include cycle: " + " -> ".join(p.include_stack + [canonical]))
    if len(p.include_stack) >= 64:
        die("include depth exceeds 64")
    p.include_stack.append(canonical)
    try:
        _parse_into(p, text, fname)
    finally:
        p.include_stack.pop()


def _parse_into(p, text, fname):
    for ln, raw in enumerate(text.splitlines(), 1):
        p.lines.append((fname, ln, raw))
    for ln, line in statements(text, fname):
        if line.startswith("tier order:"):
            tiers = [t.strip() for t in line[len("tier order:"):].split(">")]
            if len(set(tiers)) != len(tiers) or not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", t) for t in tiers):
                die(f"{fname}:{ln}: tiers must be distinct identifiers")
            if p.explicit_tiers and tiers != p.tiers:
                die(f"{fname}:{ln}: conflicting tier orders in one program")
            p.tiers = tiers; p.explicit_tiers = True
            TIER_SYMBOLS.update(p.tiers)
            continue
        m = re.match(r'^include\s+"([^"]+)"$', line)
        if m:
            inc = os.path.join(os.path.dirname(fname) or p.base_dir, m.group(1))
            if not os.path.exists(inc):
                die(f"{fname}:{ln}: include not found: {inc}")
            p.source_files.append(inc)
            with open(inc, encoding="utf-8") as source:
                parse_into(p, source.read(), inc)
            continue
        m = re.match(r'^anchor\s+([A-Za-z0-9_]+)\s+"([^"]*)"(.*)$', line)
        if m:
            rest = m.group(3)
            if m.group(1) in p.anchors:
                die(f"{fname}:{ln}: duplicate anchor {m.group(1)}")
            f = re.search(r'\bfile\s+"([^"]+)"', rest)
            h = re.search(r'\bsha256\s+"([0-9a-fA-F]+)"', rest)
            p.anchors[m.group(1)] = {"text": m.group(2),
                                     "dir": os.path.dirname(os.path.abspath(fname)) if fname != "<string>" else p.base_dir,
                                     "file": f.group(1) if f else None,
                                     "sha256": h.group(1).lower() if h else None,
                                     "used": 0, "line": (fname, ln)}
            continue
        m = re.match(r'^closed\s+([a-z][A-Za-z0-9_]*)\s+"([^"]*)"(.*)$', line)
        if m:
            rest = m.group(3)
            tier = "derived"
            tm = re.search(r"\btier\s+([A-Za-z0-9_]+)\s*$", rest)
            if tm:
                tier = tm.group(1); rest = rest[: tm.start()]
            anchors = re.findall(r"@([A-Za-z0-9_]+)", rest)
            if not anchors:
                die(f"{fname}:{ln}: a closed-world warrant needs an anchor")
            for a in anchors:
                if a not in p.anchors:
                    die(f"{fname}:{ln}: unknown anchor @{a}")
                p.anchors[a]["used"] += 1
            if tier not in p.tiers:
                die(f"{fname}:{ln}: undeclared tier '{tier}'")
            p.closed[m.group(1)] = {"text": m.group(2), "anchors": anchors, "tier": tier}
            continue
        m = re.match(r"^(open\s+)?fact\s+(.*)$", line)
        if m:
            body = m.group(2)
            tier = "derived"
            tm = re.search(r"\btier\s+([A-Za-z0-9_]+)\s*$", body)
            if tm:
                tier = tm.group(1)
                body = body[: tm.start()].strip()
            ext = re.search(r'\bfrom\s+([A-Za-z0-9_]+)\s+path\s+"([^"]+)"\s*$', body)
            extern = None
            if ext:
                body = body[: ext.start()].strip()
                holes = [i for i, ch in enumerate(unquoted(body)) if ch == "?"]
                if len(holes) != 1:
                    die(f"{fname}:{ln}: an extern fact carries exactly one `?`")
                val, srcfile = p.json_at(ext.group(1), ext.group(2), f"{fname}:{ln}")
                sym = _symbolize(val)
                i = holes[0]
                body = body[:i] + fmt_val(sym) + body[i+1:]
                extern = {"anchor": ext.group(1), "file": srcfile,
                          "path": ext.group(2), "value": val}
                p.anchors[ext.group(1)]["used"] += 1
            anchors = re.findall(r"@([A-Za-z0-9_]+)", unquoted(body))
            body = re.sub(r"@[A-Za-z0-9_,\s]+$", "", body).strip()
            atom = parse_atom(body)
            if not atom:
                die(f"{fname}:{ln}: cannot parse fact atom '{body}'")
            for a in anchors:
                if a not in p.anchors:
                    die(f"{fname}:{ln}: unknown anchor @{a}")
                p.anchors[a]["used"] += 1
            if not anchors and not extern and tier != "synthetic":
                die(f"{fname}:{ln}: fact '{body}' has no anchor — anchor it or "
                    f"declare `tier synthetic`")
            if any(is_var(a) for a in atom[1]):
                die(f"{fname}:{ln}: facts must be ground")
            if tier not in p.tiers:
                die(f"{fname}:{ln}: undeclared tier '{tier}'")
            rec = {"truth": OPEN if m.group(1) else TRUE,
                             "tier": tier, "anchors": anchors,
                             "prov": {"kind": "fact", "extern": extern, "line": (fname, ln)},
                             "used": 0}
            old = p.facts.get(atom)
            supports = (old or {}).get("fact_supports", []) + [dict(rec)]
            if old is None or rec["truth"] > old["truth"] or (rec["truth"] == old["truth"] and p.stronger(tier, old["tier"])):
                p.facts[atom] = rec
            p.facts[atom]["fact_supports"] = supports
            continue
        m = re.match(r"^rule\s+([A-Za-z0-9_]+)\s*:\s*(.+?)\s*:-\s*(.+)$", line)
        if m:
            head = parse_atom(m.group(2))
            if not head:
                die(f"{fname}:{ln}: bad rule head")
            p.rules.append({"name": m.group(1), "head": head,
                            "body": parse_body(m.group(3), f"{fname}:{ln}"),
                            "fired": 0, "line": (fname, ln)})
            continue
        m = re.match(r"^defeat\s+([A-Za-z0-9_]+)\s+for\s+(.+?)\s*:-\s*(.+)$", line)
        if m:
            target = parse_atom(m.group(2))
            if not target:
                die(f"{fname}:{ln}: bad defeat target")
            p.defeats.append({"name": m.group(1), "target": target,
                              "body": parse_body(m.group(3), f"{fname}:{ln}"),
                              "line": (fname, ln)})
            continue
        m = re.match(r"^forbid\s+([A-Za-z0-9_]+)\s*:\s*(.+)$", line)
        if m:
            p.forbids.append({"name": m.group(1),
                              "body": parse_body(m.group(2), f"{fname}:{ln}"),
                              "line": (fname, ln)})
            continue
        m = re.match(r"^show\s+(.+)$", line)
        if m:
            a = parse_atom(m.group(1))
            if not a:
                die(f"{fname}:{ln}: bad show atom")
            p.shows.append(a)
            continue
        die(f"{fname}:{ln}: unrecognized statement '{line}'")


def parse(text, fname="<string>", base_dir="."):
    p = Program()
    TIER_SYMBOLS.clear()
    TIER_SYMBOLS.update(p.tiers)
    p.base_dir = base_dir
    p.source_files.append(fname)
    parse_into(p, text, fname)
    if not p.tiers:
        p.tiers = ["F0", "F1", "sworn", "native", "derived", "synthetic"]
    TIER_SYMBOLS.update(p.tiers)
    for f in p.facts.values():
        if f["tier"] not in p.tiers:
            die(f"undeclared tier '{f['tier']}'")
    validate_program(p)
    return p


def validate_program(p):
    """Reject unsafe binding order rather than silently skipping a rule."""
    if any(key[0] in META_PREDS for key in p.facts) or any(r["head"][0] in META_PREDS for r in p.rules):
        die("reflection predicates are reserved for the engine")
    def variables(args):
        return {v for v in args if is_var(v) and not v.startswith("_G")}
    for entries in (p.rules, p.forbids, p.defeats):
        names = set()
        for r in entries:
            where = "%s:%s" % r["line"]
            if r["name"] in names: die(f"{where}: duplicate rule/gate name {r['name']}")
            names.add(r["name"])
            bound = variables(r["target"][1]) if "target" in r else set()
            for kind, payload in r["body"]:
                dependency = payload if kind in ("atom", "not") else payload[2] if kind == "agg" else None
                if "head" in r and dependency and dependency[0] in META_PREDS:
                    die(f"{where}: proof reflection is available in forbids and defeaters")
                needed = set()
                if kind == "atom":
                    bound |= variables(payload[1])
                elif kind == "not":
                    needed = variables(payload[1])
                elif kind == "guard":
                    needed = expr_vars(payload[0]) | expr_vars(payload[2])
                elif kind == "bind":
                    needed = expr_vars(payload[1])
                elif kind == "agg":
                    var, fn, atom, over = payload
                    if over:
                        missing = expr_vars(expression_text(over)) - (bound | variables(atom[1]))
                        if missing:
                            die(f"{where}: aggregate expression has unbound variable(s) {', '.join(sorted(missing))}")
                if needed - bound:
                    die(f"{where}: {r['name']}: unbound variable(s) {', '.join(sorted(needed-bound))}; bind them in an earlier positive atom or expression")
                if kind in ("bind", "agg"): bound.add(payload[0])
            if "head" in r and variables(r["head"][1]) - bound:
                die(f"{where}: {r['name']}: unbound head variable(s) {', '.join(sorted(variables(r['head'][1])-bound))}")


def load(path):
    try:
        text = Path(path).read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        die(f"cannot read program {path}: {error}")
    return parse(text, path, os.path.dirname(os.path.abspath(path)))


# ---------------------------------------------------------------- eval
def subst(args, env):
    return tuple(env.get(a, a) if is_var(a) else a for a in args)


def unify(pat, ground, env):
    if len(pat) != len(ground):
        return None
    e = dict(env)
    for a, b in zip(pat, ground):
        if is_var(a):
            if a in e and e[a] != b:
                return None
            e[a] = b
        elif isinstance(a, (float, Fraction)) and isinstance(b, (float, Fraction)):
            if a != b:
                return None
        elif a != b:
            return None
    return e


def guard_val(tok, env):
    t = parse_term(tok)
    if isinstance(t, (float, Fraction)):
        return t
    if is_var(t):
        v = env.get(t)
        return v if isinstance(v, (float, Fraction)) else None
    return None


def arith(a, op, b):
    if op == "/" and b == 0:
        die("division by zero in arithmetic guard or binding")
    r = {"*": lambda: a * b, "/": lambda: a / b, "+": lambda: a + b, "-": lambda: a - b}[op]()
    if op in "+-" and isinstance(a, Date) and not isinstance(b, Date):
        return Date.from_ordinal(r)
    return r


def eval_expr(node, env):
    if node[0] == "value":
        term = node[1]
        if is_var(term) and term not in env:
            die(f"unbound expression variable {term}")
        return env[term] if is_var(term) else term
    if node[0] == "unary":
        v = eval_expr(node[2], env)
        if not isinstance(v, Fraction) or isinstance(v, Date): die("unary arithmetic requires a number")
        return v if node[1] == "+" else -v
    a, b = eval_expr(node[2], env), eval_expr(node[3], env)
    if not isinstance(a, Fraction) or not isinstance(b, Fraction):
        die("arithmetic requires numeric operands")
    op = node[1]
    if isinstance(a, Date) or isinstance(b, Date):
        if isinstance(a, Date) and isinstance(b, Date) and op == "-": return Fraction(a) - Fraction(b)
        if isinstance(a, Date) and not isinstance(b, Date) and op in ("+", "-"):
            if b.denominator != 1: die("date offsets must be whole days")
            return arith(a, op, b)
        if isinstance(b, Date) and not isinstance(a, Date) and op == "+":
            if a.denominator != 1: die("date offsets must be whole days")
            return arith(b, op, a)
        die("dates support whole-day offsets and date differences")
    return arith(a, op, b)


def sym_val(tok, env):
    t = parse_term(tok)
    return env.get(t) if is_var(t) else t


def eval_guard(g, env):
    left, op, right = g
    lv, rv = eval_expr(left, env), eval_expr(right, env)
    if op in ("==", "!="):
        same = (isinstance(lv, Date) == isinstance(rv, Date)) and lv == rv
        return same if op == "==" else not same
    if not isinstance(lv, Fraction) or not isinstance(rv, Fraction) or isinstance(lv, Date) != isinstance(rv, Date):
        die("ordered comparisons require two numbers or two dates")
    return {">": lambda: lv > rv, "<": lambda: lv < rv, ">=": lambda: lv >= rv, "<=": lambda: lv <= rv}[op]()


def eval_bind(b, env):
    v, expression = b
    rv = eval_expr(expression, env)
    if v in env and env[v] != rv:
        return None
    e = dict(env); e[v] = rv
    return e


def match_facts(p, pred, pargs, env):
    for (fp, fargs), rec in list(p.facts.items()):
        if fp != pred or len(fargs) != len(pargs):
            continue
        e = unify(pargs, fargs, env)
        if e is not None:
            yield e, rec, (fp, fargs)


def eval_body(p, body, env0=None):
    """Yields (env, truth, tiers, premises) for every satisfying binding."""
    envs = [(env0 or {}, TRUE, [], [])]
    for kind, payload in body:
        nxt = BoundedBindings(p.limits["max_bindings"])
        if kind == "guard":
            for env, tr, ts, pr in envs:
                if eval_guard(payload, env):
                    nxt.append((env, tr, ts, pr + [("guard", payload)]))
        elif kind == "bind":
            for env, tr, ts, pr in envs:
                e = eval_bind(payload, env)
                if e is not None:
                    nxt.append((e, tr, ts, pr + [("bind", (payload, e[payload[0]]))]))
        elif kind == "atom":
            pred, pargs = payload
            for env, tr, ts, pr in envs:
                for e, rec, key in match_facts(p, pred, pargs, env):
                    nxt.append((e, min(tr, rec["truth"]), ts + [rec["tier"]],
                                pr + [("atom", key)]))
        elif kind == "not":
            pred, pargs = payload
            for env, tr, ts, pr in envs:
                hits = list(match_facts(p, pred, pargs, env))
                if any(r["truth"] == TRUE for _, r, _ in hits):
                    continue                      # positively present → fails
                if hits:                          # only OPEN instances → OPEN
                    nxt.append((env, OPEN, ts + ["derived"],
                                pr + [("not", (payload, "OPEN_INSTANCE"))]))
                elif pred in p.closed:
                    c = p.closed[pred]
                    nxt.append((env, tr, ts + [c["tier"]],
                                pr + [("not", (payload, "CLOSED:" + c["text"]))]))
                else:
                    nxt.append((env, OPEN, ts + ["derived"],
                                pr + [("not", (payload, "DOMAIN_OPEN"))]))
        elif kind == "agg":
            var, fn, atom, over = payload
            pred, pargs = atom
            selected = expression_text(over) if over else None
            for env, tr, ts, pr in envs:
                hits = list(match_facts(p, pred, pargs, env))
                vals, tr2, ts2, keys = [], tr, list(ts), []
                for e, rec, key in hits:
                    tr2 = min(tr2, rec["truth"]); ts2.append(rec["tier"]); keys.append(key)
                    if over:
                        v = eval_expr(selected, e)
                        if fn != "count_distinct" and (not isinstance(v, Fraction) or isinstance(v, Date)):
                            die(f"aggregate {fn} over non-numeric {over} in {fmt_atom(key)}")
                        vals.append(v)
                if fn == "count":
                    res = Fraction(len(hits))
                elif fn == "count_distinct":
                    res = Fraction(len(set(vals)))
                elif fn == "sum":
                    res = sum(vals, Fraction(0))
                elif not vals:
                    continue
                elif fn == "avg":
                    res = sum(vals, Fraction(0)) / len(vals)
                else:
                    res = (min if fn == "min" else max)(vals)
                if var in env and env[var] != res:
                    continue
                e = dict(env); e[var] = res
                nxt.append((e, tr2, ts2, pr + [("agg", (payload, res, keys))]))
        envs = nxt
        if len(envs) > p.limits["max_bindings"]:
            die(f"evaluation limit: body bindings exceed {p.limits['max_bindings']}", 4)
        if not envs:
            break
    return envs


class BoundedBindings(list):
    def __init__(self, limit):
        super().__init__()
        self.limit = limit

    def append(self, item):
        if len(self) >= self.limit:
            die(f"evaluation limit: body bindings exceed {self.limit}", 4)
        super().append(item)


def strata(p):
    from tell_advanced import dependency_plan
    plan = dependency_plan(p)
    if not plan['stratified']:
        issue = plan['issues'][0]
        die("program is not stratified: " + issue['strict_kind'] + " cycle " +
            " -> ".join(issue['cycle']) + " in rule " + issue['rule'])
    by_name = {rule['name']: rule for rule in p.rules}
    return [[by_name[name] for name in group['rules']] for group in plan['strata']]


def fixpoint(p):
    if len(p.facts) > p.limits["max_facts"]:
        die(f"evaluation limit: facts exceed {p.limits['max_facts']}", 4)
    for rules in strata(p):
        changed = True
        while changed:
            p.rounds += 1
            if p.rounds > p.limits["max_rounds"]:
                die(f"evaluation limit: inference rounds exceed {p.limits['max_rounds']}", 4)
            changed = False
            for rule in rules:
                for env, tr, ts, pr in eval_body(p, rule["body"]):
                    key = (rule["head"][0], subst(rule["head"][1], env))
                    if any(is_var(a) for a in key[1]):
                        continue
                    tier = p.weakest(ts)
                    old = p.facts.get(key)
                    better = (old is None or tr > old["truth"] or
                              (tr == old["truth"] and p.stronger(tier, old["tier"])))
                    if better:
                        if old is None and len(p.facts) >= p.limits["max_facts"]:
                            die(f"evaluation limit: facts exceed {p.limits['max_facts']}", 4)
                        p.facts[key] = {"truth": tr, "tier": tier, "anchors": [],
                                        "prov": {"kind": "rule", "rule": rule["name"],
                                                 "premises": pr},
                                        "used": 0,
                                        "fact_supports": (old or {}).get("fact_supports", []),
                                        "derivations": (old or {}).get("derivations", {})}
                        rule["fired"] += 1
                        changed = True
                    # every derivation is remembered, not only the winning one — a gate
                    # that reads the proof graph must see the weak path too
                    rec = p.facts[key]
                    sig = (rule["name"], tuple(x[1] for x in pr if x[0] == "atom"),
                           tuple(k for x in pr if x[0] == "agg" for k in x[1][2]))
                    rec.setdefault("derivations", {})[sig] = pr
    mark_used(p)


def mark_used(p):
    for rec in p.facts.values():
        if rec["prov"]["kind"] == "rule":
            for kind, payload in rec["prov"]["premises"]:
                if kind == "atom" and payload in p.facts:
                    p.facts[payload]["used"] += 1
                elif kind == "agg":
                    for k in payload[2]:
                        if k in p.facts:
                            p.facts[k]["used"] += 1


def materialize_meta(p):
    """Reflective facts over the proof graph, for forbids and defeaters only."""
    meta = {}
    for key, rec in list(p.facts.items()):
        meta[("atom_tier", (key[0], rec["tier"]))] = True
        for support in rec.get("fact_supports", []):
            meta[("atom_tier", (key[0], support["tier"]))] = True
        proofs = list(rec.get("derivations", {}).values())
        if rec["prov"]["kind"] == "rule": proofs.append(rec["prov"]["premises"])
        for pr in proofs:
            for kind, payload in pr:
                if kind == "atom":
                    meta[("premise_of", (key[0], payload[0]))] = True
                elif kind == "agg":
                    for k in payload[2]:
                        meta[("premise_of", (key[0], k[0]))] = True
    # transitive closure of premise_of
    graph = {}
    for k in meta:
        if k[0] == "premise_of": graph.setdefault(k[1][0], set()).add(k[1][1])
    edges = set()
    for start in graph:
        seen, pending = set(), list(graph[start])
        while pending:
            end = pending.pop()
            if end in seen: continue
            seen.add(end); edges.add((start, end))
            if len(edges) > p.limits["max_bindings"]:
                die(f"evaluation limit: reflected edges exceed {p.limits['max_bindings']}", 4)
            pending.extend(graph.get(end, set()) - seen)
    for a, b in edges:
        meta[("premise_of", (a, b))] = True
    for i, t1 in enumerate(p.tiers):
        for t2 in p.tiers[:i]:
            meta[("tier_below", (t1, t2))] = True     # t1 is weaker than t2
    for k in meta:
        p.facts[k] = {"truth": TRUE, "tier": "derived", "anchors": [],
                      "prov": {"kind": "meta"}, "used": 0}


def strip_meta(p):
    for k in [k for k in p.facts if p.facts[k]["prov"]["kind"] == "meta"]:
        del p.facts[k]


def check_forbids(p):
    materialize_meta(p)
    hits = []
    for f in p.forbids:
        sols = eval_body(p, f["body"])
        if any(tr == TRUE for _, tr, _, _ in sols):
            hits.append((f["name"], next(s for s in sols if s[1] == TRUE)))
    strip_meta(p)
    return hits


def apply_defeaters(p):
    materialize_meta(p)
    for d in p.defeats:
        pred, pargs = d["target"]
        for env, rec, key in list(match_facts(p, pred, pargs, {})):
            if rec["prov"]["kind"] == "meta":
                continue
            sols = eval_body(p, d["body"], env)
            if not sols:
                rec.setdefault("defeat_checked", []).append((d["name"], "ABSENT"))
                continue
            best = max(tr for _, tr, _, _ in sols)
            if best == TRUE:
                rec["defeated_by"] = d["name"]
                rec["defeat_prov"] = sols[0][3]
            else:
                rec["truth"] = min(rec["truth"], OPEN)
                rec["annotated_by"] = d["name"]
                rec["defeat_prov"] = sols[0][3]
    strip_meta(p)


def status(rec):
    if rec.get("defeated_by"):
        return "DEFEATED"
    return "HOLD" if rec["truth"] == TRUE else "HOLD_WITH_OPEN"


# ---------------------------------------------------------------- output
def fmt_val(x):
    if isinstance(x, Quoted):
        return json.dumps(str(x), ensure_ascii=False)
    if isinstance(x, Date):
        return str(x)
    if isinstance(x, Fraction):
        # Exact decimal when terminating; otherwise an explicit rational.
        d = x.denominator
        while d % 2 == 0: d //= 2
        while d % 5 == 0: d //= 5
        if d != 1: return str(x)
        from decimal import localcontext
        with localcontext() as ctx:
            ctx.prec = max(50, len(str(abs(x.numerator))) + len(str(x.denominator)) * 4 + 4)
            text = format(Decimal(x.numerator) / Decimal(x.denominator), "f")
        return text.rstrip("0").rstrip(".") if "." in text else text
    if isinstance(x, float):
        return "%g" % x
    return str(x)


def fmt_atom(a):
    pred, args = a
    return pred if not args else "%s(%s)" % (pred, ", ".join(fmt_val(x) for x in args))


def anchor_text(p, rec):
    parts = [p.anchors[a]["text"] for a in rec["anchors"] if a in p.anchors]
    ext = rec["prov"].get("extern")
    if ext:
        parts.append("%s#%s = %s" % (ext["file"], ext["path"], ext["value"]))
    return "; ".join(parts) or "(synthetic)"


def fmt_premise(kind, payload):
    if kind == "guard":
        left, op, right = payload
        return f"guard {fmt_expr(left)} {op} {fmt_expr(right)}  [holds]"
    if kind == "bind":
        (v, expr), val = payload
        return f"let {v} = {fmt_expr(expr)}  → {fmt_val(val)}"
    if kind == "not":
        atom, how = payload
        return f"not {fmt_atom(atom)}  [{how}]"
    if kind == "agg":
        (var, fn, atom, over), res, keys = payload
        return f"{var} = {fn}({fmt_atom(atom)}{', ' + over if over else ''})  → {fmt_val(res)} over {len(keys)}"
    return "?"


def why(p, atom, depth=0, out=None, seen=None):
    out = out if out is not None else []
    seen = seen if seen is not None else set()
    rec = p.facts.get(atom)
    pad = "  " * depth
    if rec is None:
        out.append(pad + fmt_atom(atom) + "  — NOT DERIVED")
        return out
    st = status(rec)
    if rec["prov"]["kind"] == "fact":
        out.append(f"{pad}{fmt_atom(atom)}  [{st} · {TRUTH_NAME[rec['truth']]} · {rec['tier']}]  ⚓ {anchor_text(p, rec)}")
        if rec.get("defeated_by") or rec.get("annotated_by"):
            out.append(pad + "  " + ("DEFEATED by " if rec.get("defeated_by") else "ANNOTATED by ") + (rec.get("defeated_by") or rec["annotated_by"]))
        return out
    out.append(f"{pad}{fmt_atom(atom)}  [{st} · {rec['tier']}]  ← rule {rec['prov']['rule']}")
    if atom in seen:
        return out
    seen.add(atom)
    for kind, payload in rec["prov"]["premises"]:
        if kind == "atom":
            why(p, payload, depth + 1, out, seen)
        elif kind == "agg":
            out.append("  " * (depth + 1) + fmt_premise(kind, payload))
            for k in payload[2]:
                why(p, k, depth + 2, out, seen)
        else:
            out.append("  " * (depth + 1) + fmt_premise(kind, payload))
    if rec.get("defeated_by") or rec.get("annotated_by"):
        tag = "DEFEATED by" if rec.get("defeated_by") else "ANNOTATED by"
        out.append("  " * (depth + 1) + f"✗ {tag} {rec.get('defeated_by') or rec.get('annotated_by')}:")
        for kind, payload in rec.get("defeat_prov", []):
            if kind == "atom":
                why(p, payload, depth + 2, out, seen)
            else:
                out.append("  " * (depth + 2) + fmt_premise(kind, payload))
    return out


def resolve(p, atom):
    """A show/why atom may carry variables: every derived instance that unifies is reported."""
    if not any(is_var(a) for a in atom[1]):
        return [atom]
    return sorted((k for _, _, k in match_facts(p, atom[0], atom[1], {})), key=fmt_atom)


def report_atoms(p):
    if not p.shows:
        return sorted(k for k in p.facts if p.facts[k]["prov"]["kind"] == "rule")
    out = []
    for a in p.shows:
        hits = resolve(p, a)
        out.extend(hits if hits else [a])
    return out


def source_status(p):
    rows = []
    for name, anchor in p.anchors.items():
        if not anchor.get("file"): continue
        fp = os.path.join(anchor.get("dir", p.base_dir), anchor["file"])
        actual = p._read_sources.get(fp)
        read = actual is not None
        if actual is None and os.path.isfile(fp): actual = sha256_file(fp)
        state = "MISSING" if actual is None else "UNPINNED" if not anchor["sha256"] else "MATCH" if anchor["sha256"] == actual else "PIN_MISMATCH"
        rows.append({"anchor": name, "file": anchor["file"], "state": state,
                     "pinned_sha256": anchor["sha256"], "observed_sha256": actual,
                     "observation": "BYTES_READ" if read else "FILE_CHECK"})
    return rows


def input_snapshot(path, limits=None, strict_sources=False):
    p = load(path)
    if limits:
        p.limits.update(limits)
    sources = source_status(p)
    if strict_sources and any(s["state"] != "MATCH" for s in sources):
        die("strict source check: " + ", ".join(s["anchor"] + "=" + s["state"] for s in sources if s["state"] != "MATCH"))
    for source in sources:
        if source["state"] in ("MISSING", "PIN_MISMATCH"):
            sys.stderr.write("tell: source " + source["anchor"] + " " + source["state"] + "; inspect with verify\n")
    return p


def evaluated(path, limits=None, strict_sources=False):
    p = input_snapshot(path, limits, strict_sources)
    fixpoint(p)
    hits = check_forbids(p)
    if hits:
        sys.stderr.write("FORBID VIOLATED: %s\nLAYER WITHHELD — nothing emitted. "
                         "Fix the program or the facts.\n" % ", ".join(h[0] for h in hits))
        for name, (env, tr, ts, pr) in hits:
            sys.stderr.write(f"  {name} satisfied by: " +
                             "; ".join(fmt_atom(x[1]) if x[0] == "atom" else fmt_premise(*x)
                                       for x in pr) + "\n")
        sys.exit(3)
    apply_defeaters(p)
    return p


def run(path, why_atom=None, json_out=None, md_out=None, limits=None, strict_sources=False):
    if why_atom and parse_atom(why_atom) is None:
        die("--why requires an atom, for example balance(Project, Amount)")
    p = evaluated(path, limits, strict_sources)
    lines = []
    for a in report_atoms(p):
        rec = p.facts.get(a)
        if rec is None:
            lines.append(f"{fmt_atom(a)}  — NOT DERIVED"); continue
        tag = status(rec)
        extra = f" (by {rec['defeated_by']})" if rec.get("defeated_by") else \
                f" (annotated by {rec['annotated_by']})" if rec.get("annotated_by") else ""
        lines.append(f"{fmt_atom(a)}  {tag}{extra}  · tier {rec['tier']}")
    print("\n".join(lines))
    n_ext = sum(1 for r in p.facts.values() if r["prov"].get("extern"))
    print(f"\n{len(p.facts)} atoms · {len(p.rules)} rules · {len(p.forbids)} forbids checked clean"
          f" · {len(p.defeats)} defeaters run · {n_ext} extern facts read from source")
    if why_atom:
        a = parse_atom(why_atom)
        for inst in (resolve(p, a) or [a]):
            print("\nWHY " + fmt_atom(inst))
            print("\n".join(why(p, inst)))
    if json_out:
        with open(json_out, "w", encoding="utf-8") as target:
            json.dump(run_json(p, path), target, indent=1)
        print(f"wrote {json_out}")
    if md_out:
        with open(md_out, "w", encoding="utf-8") as target:
            target.write(run_md(p, path))
        print(f"wrote {md_out}")
    return p


def run_json(p, path):
    dump = {}
    for k, v in p.facts.items():
        d = {"truth": TRUTH_NAME[v["truth"]], "status": status(v), "tier": v["tier"],
             "kind": v["prov"]["kind"], "rule": v["prov"].get("rule"),
             "anchors": [p.anchors[x]["text"] for x in v["anchors"]]}
        if v["prov"].get("extern"):
            d["extern"] = dict(v["prov"]["extern"])
            raw_value = d["extern"]["value"]
            if isinstance(raw_value, (Decimal, Fraction)):
                d["extern"]["value"] = str(raw_value) if isinstance(raw_value, Decimal) else fmt_val(raw_value)
                d["extern"]["value_encoding"] = "exact_decimal" if isinstance(raw_value, Decimal) else "exact_rational_or_decimal"
        if v["prov"]["kind"] == "rule":
            d["premises"] = [fmt_atom(x[1]) if x[0] == "atom" else fmt_premise(*x)
                             for x in v["prov"]["premises"]]
            d["premise_atoms"] = [fmt_atom(x[1]) for x in v["prov"]["premises"] if x[0] == "atom"] + \
                                 [fmt_atom(k) for x in v["prov"]["premises"] if x[0] == "agg" for k in x[1][2]]
        if v.get("defeated_by"):
            d["defeated_by"] = v["defeated_by"]
        if v.get("annotated_by"):
            d["annotated_by"] = v["annotated_by"]
        if len(v.get("fact_supports", [])) > 1:
            d["fact_supports"] = support_rows(p, v)
        dump[fmt_atom(k)] = d
    return {"schema": "tell_run.v2", "runtime_version": VERSION, "evaluation": {"rounds": p.rounds, "limits": p.limits}, "program": os.path.basename(path),
            "program_sha256": sha256_file(path), "tiers": p.tiers,
            "anchors": {k: {"text": v["text"], "file": v["file"], "sha256": v["sha256"]}
                        for k, v in p.anchors.items()},
            "closed_predicates": p.closed, "source_status": source_status(p), "atoms": dump}


def support_rows(p, rec):
    return [{"truth": TRUTH_NAME[s["truth"]], "tier": s["tier"],
             "anchors": list(s["anchors"]), "source": anchor_text(p, s),
             "line": s["prov"].get("line")} for s in rec.get("fact_supports", [])]


def body_text(kind, payload):
    if kind == "atom": return fmt_atom(payload)
    if kind == "not": return "not " + fmt_atom(payload)
    if kind == "guard": return fmt_expr(payload[0]) + " " + payload[1] + " " + fmt_expr(payload[2])
    if kind == "bind": return str(payload[0]) + " = " + fmt_expr(payload[1])
    var, fn, atom, over = payload
    return f"{var} = {fn}({fmt_atom(atom)}" + (", " + over if over else "") + ")"


def missing_routes(p, goal, limit=20):
    """First blocking item for each tested route to a ground goal; never infer falsity."""
    if any(is_var(a) for a in goal[1]):
        return [{"state": "GROUND_QUERY_REQUIRED", "detail": "Bind the query arguments to inspect missing routes."}]
    routes, remaining = [], limit
    for rule in p.rules:
        if rule["head"][0] != goal[0]: continue
        env0 = unify(rule["head"][1], goal[1], {})
        if env0 is None: continue
        active = [env0]
        for kind, payload in rule["body"]:
            next_envs = []
            for env in active:
                if remaining <= 0:
                    return routes + [{"state": "ROUTES_TRUNCATED", "limit": limit}]
                remaining -= 1
                sols = eval_body(p, [(kind, payload)], env)
                if sols:
                    for e, _, _, _ in sols:
                        next_envs.append(e)
                else:
                    state = {"atom": "MISSING_PREMISE", "guard": "GUARD_FAILED", "bind": "BINDING_CONFLICT", "not": "NEGATION_BLOCKED", "agg": "AGGREGATE_EMPTY_OR_CONFLICT"}[kind]
                    item = body_text(kind, payload)
                    if kind in ("atom", "not"):
                        item = ("not " if kind == "not" else "") + fmt_atom((payload[0], subst(payload[1], env)))
                    routes.append({"rule": rule["name"], "state": state, "item": item,
                                   "bindings": {str(k): fmt_val(v) for k, v in env.items() if not k.startswith("_G")},
                                   "line": rule["line"]})
            active = next_envs
            if not active: break
        if active:
            routes.append({"rule": rule["name"], "state": "ROUTE_MATCHES", "line": rule["line"]})
    return routes or [{"state": "NO_MATCHING_RULE", "detail": "No rule head matches this ground query in the loaded program."}]


def query_json(p, goal, limit=100):
    if limit < 1: die("query limit must be a positive integer")
    found = sorted(match_facts(p, goal[0], goal[1], {}), key=lambda row: fmt_atom(row[2]))
    rows = []
    for env, rec, key in found[:limit]:
        rows.append({"atom": fmt_atom(key), "status": status(rec), "truth": TRUTH_NAME[rec["truth"]],
                     "tier": rec["tier"], "bindings": {str(k): fmt_val(v) for k, v in env.items() if not k.startswith("_G")},
                     "why": why(p, key), "fact_supports": support_rows(p, rec),
                     "defeated_by": rec.get("defeated_by"), "annotated_by": rec.get("annotated_by")})
    return {"schema": "tell_query.v3", "runtime_version": VERSION, "query": fmt_atom(goal),
            "state": "MATCHES" if found else "UNRESOLVED", "count": len(found), "truncated": len(found) > limit,
            "matches": rows, "missing_routes": [] if found else missing_routes(p, goal),
            "source_status": source_status(p), "evaluation": {"rounds": p.rounds, "limits": p.limits},
            "coverage": {"program_files": list(p.source_files), "scope": "loaded program and its entered facts and rules"}}


def query(path, goal_text, as_json=False, show_why=False, limit=100, limits=None, strict_sources=False):
    p = evaluated(path, limits, strict_sources)
    goal = parse_atom(goal_text)
    if goal is None: die("query requires an atom, for example balance(Project, Amount)")
    data = query_json(p, goal, limit)
    if as_json:
        print(json.dumps(data, indent=2, ensure_ascii=False))
    else:
        for row in data["matches"]:
            print(f"{row['atom']}  {row['status']}  · tier {row['tier']}")
            if row["bindings"]: print("  " + ", ".join(k + " = " + v for k, v in row["bindings"].items()))
            if show_why: print("\n".join("  " + line for line in row["why"]))
        if not data["matches"]:
            print(fmt_atom(goal) + "  UNRESOLVED")
            for route in data["missing_routes"]:
                print("  " + route.get("rule", "query") + ": " + route["state"] + " — " + route.get("item", route.get("detail", "")))
        if data["truncated"]: print(f"showing {limit} of {data['count']} matches")
    return data


def run_md(p, path):
    L = [f"# TELL run — `{os.path.basename(path)}`", "",
         f"program sha256 `{sha256_file(path)[:16]}` · tiers `{' > '.join(p.tiers)}`", ""]
    L += ["## Conclusions", "", "| atom | status | tier | rule |", "|---|---|---|---|"]
    for a in report_atoms(p):
        rec = p.facts.get(a)
        if rec is None:
            L.append(f"| `{fmt_atom(a)}` | NOT DERIVED | — | — |"); continue
        st = status(rec) + (f" by {rec['defeated_by']}" if rec.get("defeated_by") else "") \
             + (f" (annotated by {rec['annotated_by']})" if rec.get("annotated_by") else "")
        L.append(f"| `{fmt_atom(a)}` | {st} | {rec['tier']} | {rec['prov'].get('rule', '')} |")
    ext = [(k, v) for k, v in p.facts.items() if v["prov"].get("extern")]
    if ext:
        L += ["", "## Extern facts (read from source at run time)", "",
              "| atom | file | path | value |", "|---|---|---|---|"]
        for k, v in ext:
            e = v["prov"]["extern"]
            L.append(f"| `{fmt_atom(k)}` | {e['file']} | `{e['path']}` | {e['value']} |")
    opens = [(k, v) for k, v in p.facts.items() if v["truth"] == OPEN]
    if opens:
        L += ["", "## Open items (annotate, never downgrade)", "", "| atom | kind | anchor |", "|---|---|---|"]
        for k, v in opens:
            L.append(f"| `{fmt_atom(k)}` | {v['prov']['kind']} | {anchor_text(p, v) if v['prov']['kind']=='fact' else v.get('annotated_by') or v['prov'].get('rule')} |")
    L += ["", "## Gates", "", "| gate | kind | result |", "|---|---|---|"]
    for f in p.forbids:
        L.append(f"| {f['name']} | forbid | clean |")
    for d in p.defeats:
        recs = [rec for _, rec, _ in match_facts(p, d["target"][0], d["target"][1], {})]
        r = "target not derived" if not recs else ("FIRED" if any(x.get("defeated_by") == d["name"] for x in recs)
             else "annotates" if any(x.get("annotated_by") == d["name"] for x in recs) else "absent — target holds")
        L.append(f"| {d['name']} | defeater for `{fmt_atom(d['target'])}` | {r} |")
    by_tier = {}
    for v in p.facts.values():
        if v["prov"]["kind"] == "fact":
            by_tier[v["tier"]] = by_tier.get(v["tier"], 0) + 1
    L += ["", "## Facts by tier", "", "| tier | facts |", "|---|---|"]
    for t in p.tiers:
        if t in by_tier:
            L.append(f"| {t} | {by_tier[t]} |")
    L += ["", "## Anchors", "", "| name | text | file | pinned |", "|---|---|---|---|"]
    for k, v in p.anchors.items():
        pin = "—" if not v["file"] else ("sha " + v["sha256"][:12] if v["sha256"] else "UNPINNED")
        L.append(f"| {k} | {v['text']} | {v['file'] or ''} | {pin} |")
    return "\n".join(L) + "\n"


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


# ---------------------------------------------------------------- lint / verify / diff
def lint(path, strict=False, limits=None):
    p = load(path)
    if limits: p.limits.update(limits)
    findings = []
    heads = {r["head"][0] for r in p.rules}
    fact_preds = {k[0] for k in p.facts}
    known = heads | fact_preds | set(META_PREDS)
    for r in p.rules:
        for kind, payload in r["body"]:
            pred = payload[0] if kind in ("atom", "not") else payload[2][0] if kind == "agg" else None
            if pred and pred not in known:
                findings.append(("TYPO_OR_ORPHAN", f"rule {r['name']}: predicate '{pred}' appears in no fact and no rule head"))
    for f in p.forbids:
        preds = [pl[0] if k in ("atom", "not") else pl[2][0] for k, pl in f["body"] if k in ("atom", "not", "agg")]
        dead = [q for q in preds if q not in known]
        if dead:
            findings.append(("VACUOUS_FORBID", f"forbid {f['name']}: '{', '.join(dead)}' can never be derived — the gate cannot fire. A gate that does not block is not a gate."))
    for d in p.defeats:
        preds = [pl[0] if k in ("atom", "not") else pl[2][0] for k, pl in d["body"] if k in ("atom", "not", "agg")]
        dead = [q for q in preds if q not in known]
        if dead:
            findings.append(("VACUOUS_DEFEATER", f"defeat {d['name']}: '{', '.join(dead)}' can never be derived"))
        if d["target"][0] not in heads and d["target"][0] not in fact_preds:
            findings.append(("DEFEATER_NO_TARGET", f"defeat {d['name']}: target {fmt_atom(d['target'])} is never derived"))
    fixpoint(p)
    for r in p.rules:
        if not r["fired"]:
            findings.append(("DEAD_RULE", f"rule {r['name']} never fired"))
    gate_preds = set()
    for g in p.forbids + p.defeats:
        for kind, pl in g["body"]:
            if kind in ("atom", "not"):
                gate_preds.add(pl[0])
            elif kind == "agg":
                gate_preds.add(pl[2][0])
    for r in p.rules:
        for kind, pl in r["body"]:
            if kind == "not":
                gate_preds.add(pl[0])
    shown = set()
    for a in p.shows:
        shown.update(resolve(p, a))
    for k, v in p.facts.items():
        if v["prov"]["kind"] == "fact" and v["used"] == 0 and k not in shown and k[0] not in gate_preds:
            findings.append(("UNUSED_FACT", f"fact {fmt_atom(k)} is read by no rule, gate or negation and never shown"))
    for a in p.shows:
        if not resolve(p, a):
            findings.append(("SHOW_NOT_DERIVED", f"show {fmt_atom(a)}: never derived"))
    for k, v in p.anchors.items():
        if v["used"] == 0:
            findings.append(("UNUSED_ANCHOR", f"anchor {k} declared but never cited"))
        if v["file"] and not v["sha256"]:
            findings.append(("UNPINNED_ANCHOR", f"anchor {k} names file {v['file']} without a sha256 — run `verify --pin`"))
    for k, v in p.facts.items():
        if v["prov"]["kind"] == "fact" and not v["anchors"] and not v["prov"].get("extern"):
            findings.append(("SYNTHETIC_FACT", f"fact {fmt_atom(k)} is synthetic (no anchor)"))
    if not p.forbids:
        findings.append(("NO_GATE", "program declares no forbid — nothing can withhold a bad layer"))
    if not findings:
        print("lint: clean")
    for code, msg in findings:
        print(f"{code:18s} {msg}")
    print(f"\n{len(findings)} finding(s)")
    if strict and findings:
        sys.exit(1)


def verify(path, pin=False):
    p = load(path)
    rows, bad = [], 0
    for k, v in p.anchors.items():
        if not v["file"]:
            continue
        fp = os.path.join(v.get("dir", p.base_dir), v["file"])
        if not os.path.exists(fp):
            rows.append((k, v["file"], "MISSING")); bad += 1; continue
        h = sha256_file(fp)
        if v["sha256"] is None:
            rows.append((k, v["file"], "UNPINNED → " + h[:16]))
            if pin:
                _pin(p, k, h)
        elif v["sha256"] != h:
            rows.append((k, v["file"], f"MISMATCH pinned {v['sha256'][:12]} now {h[:12]}")); bad += 1
            if pin:
                _pin(p, k, h)
        else:
            rows.append((k, v["file"], "OK " + h[:12]))
    for k, v in p.facts.items():
        e = v["prov"].get("extern")
        if e:
            rows.append((fmt_atom(k), f"{e['file']}#{e['path']}", f"= {e['value']}"))
    w = max((len(r[0]) for r in rows), default=6)
    for r in rows:
        print(f"{r[0]:{w}s}  {r[1]:44s}  {r[2]}")
    print(f"\n{len(rows)} checked · {bad} problem(s)" + (" · pins written" if pin else ""))
    if bad:
        sys.exit(1)


def _pin(p, anchor, h):
    fname, ln = p.anchors[anchor]["line"]
    text = Path(fname).read_text(encoding="utf-8")
    selected = next(((start, end) for _, value, start, end in statements(text, fname, True)
                     if re.match(r"anchor\s+" + re.escape(anchor) + r"\b", value)), None)
    if selected is None: die(f"{fname}:{ln}: anchor {anchor} declaration no longer present")
    start, end = selected
    raw = text[start:end]
    if re.search(r'\bsha256\s+"[0-9a-fA-F]*"', raw):
        raw = re.sub(r'\bsha256\s+"[0-9a-fA-F]*"', f'sha256 "{h}"', raw)
    else:
        raw = re.sub(r"\.\s*(%.*)?$", lambda m: f' sha256 "{h}".' + (" " + m.group(1) if m.group(1) else ""), raw, count=1)
    Path(fname).write_text(text[:start] + raw + text[end:], encoding="utf-8")


def diff(a, b):
    for f in (a, b):
        if not os.path.exists(f):
            die(f"diff: no such run file {f}")
    A = json.loads(Path(a).read_text())["atoms"]; B = json.loads(Path(b).read_text())["atoms"]
    norm = {"TRUE": "HOLD", "OPEN": "HOLD_WITH_OPEN"}
    for D in (A, B):
        for v in D.values():
            v["status"] = v.get("status") or norm.get(v["truth"], v["truth"])
    added = sorted(set(B) - set(A)); removed = sorted(set(A) - set(B))
    changed = []
    for k in sorted(set(A) & set(B)):
        sa = A[k].get("status") or A[k]["truth"]; sb = B[k].get("status") or B[k]["truth"]
        if sa != sb or A[k]["tier"] != B[k]["tier"]:
            changed.append((k, f"{sa}·{A[k]['tier']}", f"{sb}·{B[k]['tier']}"))
    for k in added:
        print(f"+ {k}  {B[k].get('status') or B[k]['truth']} · {B[k]['tier']}")
    for k in removed:
        print(f"- {k}  {A[k].get('status') or A[k]['truth']} · {A[k]['tier']}")
    for k, x, y in changed:
        print(f"~ {k}  {x} → {y}")
    print(f"\n{len(added)} added · {len(removed)} removed · {len(changed)} changed · "
          f"{len(set(A) & set(B)) - len(changed)} identical")
    return added, removed, changed


if __name__ == "__main__":
    import argparse
    def positive(value):
        try: n = int(value)
        except ValueError: raise argparse.ArgumentTypeError("expected a positive integer")
        if n < 1: raise argparse.ArgumentTypeError("expected a positive integer")
        return n
    parser = argparse.ArgumentParser(description="TELL — exact, sourced rule reasoning")
    parser.add_argument("--version", action="version", version="TELL " + VERSION)
    commands = parser.add_subparsers(dest="command", required=True)
    for command in ("run", "query", "lint", "verify", "analyze", "scenario", "robust"):
        sub = commands.add_parser(command); sub.add_argument("file")
        if command in ("run", "query", "lint", "analyze", "scenario", "robust"):
            sub.add_argument("--max-facts", type=positive, default=20000)
            sub.add_argument("--max-rounds", type=positive, default=1000)
            sub.add_argument("--max-bindings", type=positive, default=50000)
        if command in ("run", "query", "analyze", "scenario", "robust"):
            sub.add_argument("--strict-sources", action="store_true")
        if command == "run":
            sub.add_argument("--why"); sub.add_argument("--json"); sub.add_argument("--md")
        elif command == "query":
            sub.add_argument("atom"); sub.add_argument("--json", action="store_true")
            sub.add_argument("--why", action="store_true"); sub.add_argument("--limit", type=positive, default=100)
        elif command in ("analyze", "scenario", "robust"):
            sub.add_argument("--json", action="store_true")
            if command != "analyze": sub.add_argument("atom")
            if command == "scenario":
                sub.add_argument("--assume", action="append", default=[])
                sub.add_argument("--retract", action="append", default=[])
            if command == "robust":
                sub.add_argument("--max-remove", type=int, choices=(1, 2, 3), default=2)
                sub.add_argument("--budget", type=positive, default=64)
                sub.add_argument("--input", action="append")
        elif command == "lint": sub.add_argument("--strict", action="store_true")
        else: sub.add_argument("--pin", action="store_true")
    sub = commands.add_parser("diff"); sub.add_argument("run_a"); sub.add_argument("run_b")
    args = parser.parse_args()
    limits = {k: getattr(args, k) for k in ("max_facts", "max_rounds", "max_bindings") if hasattr(args, k)}
    if args.command == "run": run(args.file, args.why, args.json, args.md, limits, args.strict_sources)
    elif args.command == "query": query(args.file, args.atom, args.json, args.why, args.limit, limits, args.strict_sources)
    elif args.command == "lint": lint(args.file, args.strict, limits)
    elif args.command == "verify": verify(args.file, args.pin)
    elif args.command == "diff": diff(args.run_a, args.run_b)

    elif args.command in ("analyze", "scenario", "robust"):
        import tell_advanced
        p = input_snapshot(args.file, limits, args.strict_sources)
        runtime = sys.modules[__name__]
        if args.command == "analyze":
            data = tell_advanced.dependency_plan(p)
            data.update(runtime_version=VERSION, source_status=source_status(p))
        elif args.command == "scenario":
            data = tell_advanced.scenario(runtime, p, args.atom, args.assume, args.retract)
            for observation in (data['baseline'], data['scenario']):
                if observation['state'] == 'GATE_BLOCKED':
                    die('FORBID VIOLATED: ' + ', '.join(observation['gates']) + '; scenario layer withheld', 3)
                if observation['state'] in ('EVALUATION_LIMIT', 'EVALUATION_ERROR'):
                    die(observation['detail'], observation['exit_code'])
        else:
            data = tell_advanced.robustness(runtime, p, args.atom, args.max_remove, args.budget, args.input)
        if args.json:
            print(json.dumps(data, indent=2, ensure_ascii=False))
        elif args.command == 'analyze':
            print('Stratified: ' + str(data['stratified']))
            for group in data['strata']:
                print('  stratum ' + str(group['level']) + ': ' + ', '.join(group['rules']))
            for issue in data['issues']:
                print('  ' + issue['code'] + ': ' + ' -> '.join(issue['cycle']))
            for warning in data['warnings']: print('  ' + warning['code'] + ': ' + warning['rule'])
        elif args.command == 'scenario':
            print('HYPOTHETICAL MODEL EXPERIMENT: ' + data['change'])
            for label in ('baseline', 'scenario'):
                observation = data[label]
                detail = ', '.join(m['atom'] + ' ' + m['status'] + ' tier ' + m['tier'] for m in observation['matches'])
                print('  ' + label + ': ' + (detail or observation['state']))
        else:
            print('HYPOTHETICAL INPUT WITHDRAWAL: ' + data['query'])
            for cut in data['minimal_cuts']:
                print('  minimal cut: ' + ', '.join(cut['removed']) + ' -> ' + cut['outcome'])
            coverage = data['coverage']
            print('  examined %s/%s candidate sets; complete within width %s: %s' %
                  (coverage['sets_examined'], coverage['candidate_sets_total'], coverage['max_remove'], coverage['complete_within_width']))
        if args.command == 'analyze' and not data['stratified']: raise SystemExit(2)
