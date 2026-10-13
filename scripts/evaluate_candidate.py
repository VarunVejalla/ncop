#!/usr/bin/env python3
"""Evaluate a Lean candidate for the two-terminal K_m Maker-Breaker game.

This script is intentionally conservative. It treats the NCop/ trusted files
as the problem statement and scores only Candidates/Candidate.lean.
"""

from __future__ import annotations

import argparse
import ast
import math
import operator
import re
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CANDIDATE = ROOT / "Candidates" / "Candidate.lean"

FORBIDDEN_PATTERNS = [
    r"\bsorry\b",
    r"\badmit\b",
    r"\baxiom\b",
    r"\bconstant\b",
    r"\bunsafe\b",
]


ALLOWED_BINOPS = {
    ast.Add: operator.add,
    ast.Sub: operator.sub,
    ast.Mult: operator.mul,
    ast.Div: operator.truediv,
}

ALLOWED_UNARYOPS = {
    ast.UAdd: operator.pos,
    ast.USub: operator.neg,
}


def eval_supported_real_expr(expr: str) -> float:
    """Evaluate the small Lean expression fragment used for scoring constants.

    Supported examples:
      2
      7 / 3
      2 + Real.sqrt 3
      2 + sqrt(3)

    This is deliberately not a Lean parser. The Lean theorem is authoritative;
    this parser only computes the score.
    """
    expr = expr.strip()
    expr = expr.replace("Real.sqrt", "sqrt")
    expr = re.sub(r"\bsqrt\s+([0-9]+(?:\.[0-9]+)?)", r"sqrt(\1)", expr)
    expr = expr.replace("^", "**")

    def visit(node: ast.AST) -> float:
        if isinstance(node, ast.Expression):
            return visit(node.body)
        if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)):
            return float(node.value)
        if isinstance(node, ast.BinOp) and type(node.op) in ALLOWED_BINOPS:
            return ALLOWED_BINOPS[type(node.op)](visit(node.left), visit(node.right))
        if isinstance(node, ast.UnaryOp) and type(node.op) in ALLOWED_UNARYOPS:
            return ALLOWED_UNARYOPS[type(node.op)](visit(node.operand))
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            if node.func.id == "sqrt" and len(node.args) == 1 and not node.keywords:
                return math.sqrt(visit(node.args[0]))
        raise ValueError(f"unsupported expression fragment: {ast.dump(node)}")

    return visit(ast.parse(expr, mode="eval"))


def parse_real_constant(text: str, name: str) -> tuple[str, float]:
    pattern = rf"def\s+{re.escape(name)}\s*:\s*(?:ℝ|Real)\s*:=\s*([^\n]+)"
    match = re.search(pattern, text)
    if not match:
        raise ValueError(f"missing `def {name} : ℝ := ...`")
    raw = match.group(1).strip()
    raw = raw.split("--", 1)[0].strip()
    try:
        value = eval_supported_real_expr(raw)
    except Exception as exc:
        raise ValueError(f"could not score `{name}` expression {raw!r}: {exc}") from exc
    return raw, value


def strip_lean_comments(text: str) -> str:
    text = re.sub(r"/-!?.*?-/", "", text, flags=re.DOTALL)
    text = re.sub(r"--.*", "", text)
    return text


def scan_candidate(text: str) -> list[str]:
    errors: list[str] = []
    for pattern in FORBIDDEN_PATTERNS:
        if re.search(pattern, text):
            errors.append(f"forbidden token matched: {pattern}")
    if "import NCop.Target" not in text:
        errors.append("candidate should import NCop.Target")
    if not re.search(r"theorem\s+lower\s*:\s*NCop\.BreakerLowerBound\s+C1", text):
        errors.append("missing theorem `lower : NCop.BreakerLowerBound C1`")
    if not re.search(r"theorem\s+upper\s*:\s*NCop\.MakerUpperBound\s+C2", text):
        errors.append("missing theorem `upper : NCop.MakerUpperBound C2`")
    return errors


def changed_trusted_files() -> list[str]:
    if not (ROOT / ".git").exists():
        return []
    proc = subprocess.run(
        ["git", "status", "--porcelain", "--", "NCop", "lakefile.lean", "lean-toolchain"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        return [f"could not inspect git status: {proc.stderr.strip()}"]
    return [line for line in proc.stdout.splitlines() if line.strip()]


def run_lake() -> tuple[bool, str]:
    lake = shutil.which("lake")
    if lake is None:
        for elan_lake in [
            Path.home() / ".elan" / "bin" / "lake.exe",
            ROOT.parents[1] / ".elan" / "bin" / "lake.exe",
        ]:
            if elan_lake.exists():
                lake = str(elan_lake)
                break
    if lake is None:
        return False, "lake executable not found on PATH"
    env = dict(**__import__("os").environ)
    if "ELAN_HOME" not in env:
        maybe_elan = Path(lake).parents[1]
        if maybe_elan.name == ".elan":
            env["ELAN_HOME"] = str(maybe_elan)
    proc = subprocess.run(
        [lake, "build", "Candidates"],
        cwd=ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return proc.returncode == 0, proc.stdout


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="emit a Python-literal result dict")
    parser.add_argument(
        "--allow-trusted-dirty",
        action="store_true",
        help="do not reject dirty trusted files; useful during initial setup",
    )
    args = parser.parse_args()

    raw_text = CANDIDATE.read_text(encoding="utf-8")
    text = strip_lean_comments(raw_text)
    errors = scan_candidate(text)

    try:
        c1_expr, c1 = parse_real_constant(text, "C1")
        c2_expr, c2 = parse_real_constant(text, "C2")
    except ValueError as exc:
        c1_expr = c2_expr = None
        c1 = c2 = None
        errors.append(str(exc))

    if c1 is not None and c2 is not None and c2 < c1:
        errors.append(f"C2 must be at least C1, got C1={c1}, C2={c2}")

    trusted_changes = changed_trusted_files()
    if trusted_changes and not args.allow_trusted_dirty:
        errors.append("trusted files are dirty:\n" + "\n".join(trusted_changes))

    build_ok = False
    build_output = ""
    if not errors:
        build_ok, build_output = run_lake()
        if not build_ok:
            errors.append(build_output)

    if errors or c1 is None or c2 is None:
        result = {
            "valid": False,
            "score": 10**9,
            "errors": errors,
        }
    else:
        gap = c2 - c1
        result = {
            "valid": build_ok,
            "C1": c1_expr,
            "C2": c2_expr,
            "C1_value": c1,
            "C2_value": c2,
            "gap": gap,
            "score": gap,
            "build_output": build_output,
        }

    if args.json:
        print(result)
    else:
        print("valid:", result["valid"])
        print("score:", result["score"])
        if "C1" in result:
            print("C1:", result["C1"])
            print("C2:", result["C2"])
            print("C1_value:", result["C1_value"])
            print("C2_value:", result["C2_value"])
            print("gap:", result["gap"])
        if result.get("errors"):
            print("errors:")
            for error in result["errors"]:
                print("-", error)

    return 0 if result["valid"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
