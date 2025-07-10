import os
import re
import sys
import logging
from typing import List, Union
from dataclasses import dataclass

# ========== Logging Setup ==========
logging.basicConfig(level=logging.ERROR, format='[%(levelname)s] %(message)s')

# ========== Regex Patterns ==========
var_regex = r'(\|[^|]*?(?:\\\|[^|]*?)*\||[^\s()]+)'
var_pattern = re.compile(var_regex)
const_regex = r'(#[xX][0-9a-fA-F]+|\d+)'
const_pattern = re.compile(const_regex)

# ========== AST Expression Node ==========
@dataclass
class ExprNode:
    """
    Represents a expression node in the SMT assert expression tree.
    
    Attributes:
        op: The operator string (e.g., 'ite', '=>', '=', 'bvule', 'extract', 'const', 'var', etc.).
        args: The arguments of the expression. Each argument can be another ExprNode.
    """
    op: str
    args: List[Union['ExprNode', str]]

    def __repr__(self):
        return f"({self.op} {' '.join(str(a) for a in self.args)})"

    def is_var(self) -> bool:
        return self.op == "var"

    def is_const(self) -> bool:
        return self.op == "const"

def is_var(expr: ExprNode) -> bool:
    return expr.op == "var" and len(expr.args) == 1

def is_const(expr: ExprNode) -> bool:
    return expr.op == "const" and len(expr.args) == 1

def is_ite(expr: ExprNode) -> bool:
    return expr.op == "ite" and len(expr.args) == 3

def is_implies(expr: ExprNode) -> bool:
    return expr.op == "=>" and len(expr.args) == 2

def is_const_true(expr: ExprNode) -> bool:
    return expr.op == "const" and len(expr.args) == 1 and expr.args[0] == "true"

def is_const_false(expr: ExprNode) -> bool:
    return expr.op == "const" and len(expr.args) == 1 and expr.args[0] == "false"

# ========== Factory Methods ==========
def make_var(name: str) -> ExprNode:
    return ExprNode("var", [name])

def make_const(val: str) -> ExprNode:
    return ExprNode("const", [val])

# ========== Tokenizer ==========
def tokenize(expr_str: str) -> List[str]:
    # tokens = re.findall(r'\(|\)|[^\s()]+', expr_str)
    # return tokens
    token_pattern = re.compile(
        r"""\s*(?:
            (?P<open>\() |
            (?P<close>\)) |
            (?P<quoted>\|(?:[^\\|]|\\.)*?\|) |  # support |...| with escapes
            (?P<atom>[^\s()]+)
        )""", re.VERBOSE
    )
    tokens = []
    for match in token_pattern.finditer(expr_str):
        kind = match.lastgroup
        token = match.group()
        tokens.append(token.strip())
    return tokens

# ========== Parse Token List → Nested S-Expression ==========
def parse_s_expr(tokens: List[str]) -> Union[str, List]:
    if not tokens:
        logging.error("Unexpected end of tokens.")
        sys.exit(1)
    token = tokens.pop(0)
    if token == '(':
        result = []
        while tokens:
            if tokens[0] == ')':
                tokens.pop(0)
                return result
            result.append(parse_s_expr(tokens))
        logging.error("Missing closing parenthesis.")
        sys.exit(1)
    elif token == ')':
        logging.error("Unexpected ')'")
        sys.exit(1)
    else:
        return token

# ========== S-Expr → ExprNode ==========
def s_expr_to_expr_node(expr: str) -> ExprNode:
    if isinstance(expr, str):
        if expr in ("true", "false"):
            return make_const(expr)
        if const_pattern.fullmatch(expr):
            return make_const(expr)
        else:
            return make_var(expr)
    elif isinstance(expr, list):
        if not expr:
            logging.error("Empty expression encountered.")
            sys.exit(1)
        op = expr[0]
        args = [s_expr_to_expr_node(e) for e in expr[1:]]
        return ExprNode(op, args)
    else:
        logging.error(f"Unsupported expression type: {type(expr)}")
        sys.exit(1)

# ========== Simplify ExprNode ==========
def simplify(expr: ExprNode) -> ExprNode:
    if isinstance(expr, str):
        return expr

    simplified_args = [simplify(arg) if isinstance(arg, ExprNode) else arg for arg in expr.args]

    # Handle 'and'
    if expr.op == "and":
        filtered = [a for a in simplified_args if not (is_const_true(a))]
        if any(is_const_false(a) for a in simplified_args):
            return make_const("false")
        if not filtered:
            return make_const("true")
        if len(filtered) == 1:
            return filtered[0]
        return ExprNode("and", filtered)

    # Handle 'or'
    elif expr.op == "or":
        filtered = [a for a in simplified_args if not (is_const_false(a))]
        if any(is_const_true(a) for a in simplified_args):
            return make_const("true")
        if not filtered:
            return make_const("false")
        if len(filtered) == 1:
            return filtered[0]
        return ExprNode("or", filtered)

    # Handle 'ite'
    elif expr.op == "ite":
        cond, then_branch, else_branch = simplified_args
        if is_const_true(cond):
            return then_branch
        elif is_const_false(cond):
            return else_branch
        return ExprNode("ite", [cond, then_branch, else_branch])

    # Handle '=>'
    elif expr.op == "=>":
        lhs, rhs = simplified_args
        if is_const_true(lhs):
            return rhs
        elif is_const_true(rhs):
            return make_const("true")
        elif is_const_false(rhs):
            return ExprNode("not", [lhs])
        return ExprNode("=>", [lhs, rhs])

    # Default: return simplified expression
    return ExprNode(expr.op, simplified_args)

# ========== Main Entry Function ==========
def parse_smt_assert_expression(smt_lines: List[str]) -> List[ExprNode]:
    exprnodes = []

    for smt_line in smt_lines:
        smt_line = smt_line.strip()
        if smt_line.startswith("(assert") and smt_line.endswith(")"):
            smt_line = smt_line[len("(assert"):-len(")")].strip()
        else:
            print(smt_line)
            continue

        try:
            tokens = tokenize(smt_line)
            s_expr = parse_s_expr(tokens)
            exprnode = s_expr_to_expr_node(s_expr)
            exprnodes.append(simplify(exprnode))
        except Exception as e:
            logging.error(f"Parsing failed: {e}")
            sys.exit(1)

    return exprnodes

# ========== Example Usage ==========
if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python exprnode.py /your/path/to/work/directory")
        exit(1)

    path = sys.argv[1]
    smt_encoding_file = os.path.join(path, 'inlined_smt_encoding.smt2')

    with open(smt_encoding_file, 'r', encoding='utf-8') as f:
        smt_encoding = f.read()
        smt_lines = smt_encoding.splitlines()

    exprnodes = parse_smt_assert_expression(smt_lines)
    for exprnode in exprnodes:
        print(exprnode)
