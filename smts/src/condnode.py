import os
import re
import sys
import logging
from typing import List, Set, Dict, Union, Optional
from dataclasses import dataclass


var_regex = r'(\|[^|]*?(?:\\\|[^|]*?)*\||[^\s()]+)'
var_pattern = re.compile(var_regex)
const_regex = r'(#[xX][0-9a-fA-F]+|\d+)'
const_pattern = re.compile(const_regex)


@dataclass
class ExprNode:
    def __init__(self, op: str, args: List[Union['ExprNode', str]]):
        self.op = op
        self.args = args

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

def is_implies_todo(expr: ExprNode) -> bool:
    """ (ite (or ...) (or ...)) """
    return expr.op == "=>" and len(expr.args) == 2 and  \
        expr.args[0].op == "or" and expr.args[1].op == "or"

def is_const_true(expr: ExprNode) -> bool:
    return expr.op == "const" and len(expr.args) == 1 and expr.args[0] == "true"

def is_const_false(expr: ExprNode) -> bool:
    return expr.op == "const" and len(expr.args) == 1 and expr.args[0] == "false"

def make_var(name: str) -> ExprNode:
    return ExprNode("var", [name])

def make_const(val: str) -> ExprNode:
    return ExprNode("const", [val])

def make_and(lhs: ExprNode, rhs: ExprNode) -> ExprNode:
    if lhs == None:
        return rhs
    elif rhs == None:
        return lhs
    else:
        return ExprNode("and", [lhs, rhs])


@dataclass
class CondNode:
    def __init__(
        self,
        expr_id: int,
        cond_expr: ExprNode,
        equal_exprs: Dict[str, ExprNode],
        inequal_exprs : Dict[str, ExprNode],
        inherited_equal_exprs: Optional[Dict[str, ExprNode]] = None,
        inherited_inequal_exprs: Optional[Dict[str, ExprNode]] = None
    ):
        self.expr_id = expr_id
        self.cond_expr = cond_expr
        self.equal_exprs = equal_exprs
        self.inequal_exprs = inequal_exprs

        self.inherited_equal_exprs = inherited_equal_exprs or {}
        self.inherited_inequalities = inherited_inequal_exprs or {}

    def __repr__(self) -> str:
        return (
            # f"expr_id=({self.expr_id}), "
            f"CondNode(cond_expr={self.cond_expr}, "
            f"equal_exprs={self.equal_exprs}, "
            f"inequal_exprs={self.inequal_exprs})"
            # f"inherited_equal_exprs={self.inherited_equal_exprs}\n"
            # f"inherited_inequal_exprs={self.inherited_inequal_exprs}\n"
        )


class ExprNodeExtractor:
    def __init__(self):
        self.expr_nodes: List[ExprNode] = []

    def parse(self, smt_lines: List[str]):
        for smt_line in smt_lines:
            smt_line = smt_line.strip()
            if smt_line.startswith("(assert") and smt_line.endswith(")"):
                smt_line = smt_line[len("(assert"):-len(")")].strip()
            else:
                print(smt_line)
                continue
    
            try:
                tokens = self.tokenize(smt_line)
                s_expr = self.parse_s_expr(tokens)
                expr_node = self.s_expr_to_expr_node(s_expr)
                self.expr_nodes.append(self.simplify(expr_node))
            except Exception as e:
                logging.error(f"Parsing failed: {e}")
                sys.exit(1) 

    def tokenize(self, expr_str: str) -> List[str]:
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

    def parse_s_expr(self, tokens: List[str]) -> Union[str, List]:
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
                result.append(self.parse_s_expr(tokens))
            logging.error("Missing closing parenthesis.")
            sys.exit(1)
        elif token == ')':
            logging.error("Unexpected ')'")
            sys.exit(1)
        else:
            return token

    def s_expr_to_expr_node(self, expr: str) -> ExprNode:
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
            args = [self.s_expr_to_expr_node(e) for e in expr[1:]]
            return ExprNode(op, args)
        else:
            logging.error(f"Unsupported expression type: {type(expr)}")
            sys.exit(1)

    def simplify(self, expr: ExprNode) -> ExprNode:
        if isinstance(expr, str):
            return expr
    
        simplified_args = [self.simplify(arg) if isinstance(arg, ExprNode) else arg for arg in expr.args]
    
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

    def get_exprnodes(self):
        return self.expr_nodes


class CondNodeExtractor:
    def __init__(self):
        self.cond_nodes: List[CondNode] = []

    def parse(self, cond_expr: ExprNode, target_expr: ExprNode, expr_id: int):
        """
        Parse under condition `cond_expr` that `target_expr` holds.
        Either cond_expr is a concrete expression like (= x 1), or an 'and' of such.
        """
        if self.is_equality_or_inequality(target_expr):
            # Base case: target_expr is equality / inequality expression
            equal_exprs = self.extract_equal_exprs(target_expr)
            inequal_exprs = self.extract_inequal_exprs(target_expr)
            self.cond_nodes.append(CondNode(expr_id, cond_expr, equal_exprs, inequal_exprs))
        elif target_expr.op == "and":
            for sub in target_expr.args:
                self.parse(cond_expr, sub, expr_id)
        elif target_expr.op == "ite":
            self.parse_ite(target_expr, expr_id, cond_expr)
        elif target_expr.op == "=>":
            self.parse_implies(target_expr, expr_id, cond_expr)
        else:
            logging.error(f"[UNSUPPORTED TARGET_EXPR] {target_expr}")
            sys.exit(1)

    def handle_top_level(self, expr: ExprNode, expr_id: int):
        if expr.op == "ite":
            self.parse_ite(expr, expr_id, inherited_cond=None)
        elif expr.op == "=>":
            self.parse_implies(expr, expr_id, inherited_cond=None)
        else:
            logging.error(f"[UNSUPPORTED TOP-LEVEL] {expr}")
            # sys.exit(1)

    def parse_ite(self, expr: ExprNode, expr_id: int, inherited_cond=None):
        cond_expr, then_expr, else_expr = expr.args

        if cond_expr.op == "and":
            for sub in cond_expr.args:
                false_cond = ExprNode("=", [sub, make_const("false")])
                self.parse(make_and(inherited_cond, false_cond), else_expr, expr_id)
            true_cond = ExprNode("=", [cond_expr, make_const("true")])
            self.parse(make_and(inherited_cond, true_cond), then_expr, expr_id)

        elif cond_expr.op == "or":
            for sub in cond_expr.args:
                true_cond = ExprNode("=", [sub, make_const("true")])
                self.parse(make_and(inherited_cond, true_cond), then_expr, expr_id)
            false_cond = ExprNode("=", [cond_expr, make_const("false")])
            self.parse(make_and(inherited_cond, false_cond), else_expr, expr_id)

        elif cond_expr.op == "=":
            true_cond = ExprNode("=", [cond_expr, make_const("true")])
            false_cond = ExprNode("=", [cond_expr, make_const("false")])
            self.parse(make_and(inherited_cond, true_cond), then_expr, expr_id)
            self.parse(make_and(inherited_cond, false_cond), else_expr, expr_id)

        elif cond_expr.op == "var":
            v = cond_expr.args[0]
            true_cond = ExprNode("=", [v, make_const("true")])
            false_cond = ExprNode("=", [v, make_const("false")])
            self.parse(make_and(inherited_cond, true_cond), then_expr, expr_id)
            self.parse(make_and(inherited_cond, false_cond), else_expr, expr_id)

        elif cond_expr.op == "ite":
            self.parse_ite(cond_expr, expr_id, inherited_cond=inherited_cond)

        elif cond_expr.op == "=>":
            self.parse_implies(cond_expr, expr_id, inherited_cond=inherited_cond)

        else:
            logging.error(f"[ITE Unsupported condition op={cond_expr.op}]")
            sys.exit(1)

    def parse_implies(self, expr: ExprNode, expr_id: int, inherited_cond=None):
        ante, cons = expr.args

        if ante.op == "and":
            true_cond = ExprNode("=", [ante, make_const("true")])
            self.parse(make_and(inherited_cond, true_cond), cons, expr_id)

        elif ante.op == "or":
            for sub in ante.args:
                true_cond = ExprNode("=", [sub, make_const("true")])
                self.parse(make_and(inherited_cond, true_cond), cons, expr_id)

        elif ante.op == "=":
            true_cond = ExprNode("=", [ante, make_const("true")])
            self.parse(make_and(inherited_cond, true_cond), cons, expr_id)

        elif ante.op == "var":
            v = ante.args[0]
            true_cond = true_cond = ExprNode("=", [v, make_const("true")])
            self.parse(make_and(inherited_cond, true_cond), cons, expr_id)

        elif ante.op == "ite":
            self.parse_ite(expr, expr_id, inherited_cond)

        elif ante.op == "=>":
            self.parse_implies(expr, expr_id, inherited_cond)

        elif ante.op == "not":
            inner = ante.args[0]
            if inner.op == "and":
                # (not (and e1 e2)) → (or (not e1) (not e2)) → (or (= e1 false) (= e2 false))
                for sub in inner.args:
                    false_cond = ExprNode("=", [sub, make_const("false")])
                    self.parse(make_and(inherited_cond, false_cond), cons, expr_id)
            elif inner.op == "or":
                # (not (or e1 e2)) → (and (not e1) (not e2)) → (and (= e1 false) (= e2 false))
                false_conds = [ExprNode("=", [sub, make_const("false")]) for sub in inner.args]
                full_cond = make_and(inherited_cond, make_and(*false_conds))
                self.parse(full_cond, cons, expr_id)
            elif inner.op == "=":
                # (not (= a b)) → store as inequality (≠), currently use (= (= a b) false)
                neq_cond = ExprNode("=", [inner, make_const("false")])
                self.parse(make_and(inherited_cond, neq_cond), cons, expr_id)
            elif inner.op == "ite":
                # Transform: (not (ite c t e)) → (ite c (not t) (not e))
                c, t, e = inner.args
                new_then = ExprNode("not", [t])
                new_else = ExprNode("not", [e])
                new_expr = ExprNode("ite", [c, new_then, new_else])
                self.parse(inherited_cond, new_expr, expr_id)
            elif inner.op == "=>":
                # Transform: (not (=> A B)) → (and A (not B))
                A, B = inner.args
                not_B = ExprNode("not", [B])
                full_cond = make_and(inherited_cond, A, not_B)
                self.parse(full_cond, make_const("true"), expr_id)
            elif inner.op == "var":
                # default: treat as simple variable expression
                false_cond = ExprNode("=", [inner, make_const("false")])
                self.parse(make_and(inherited_cond, false_cond), cons, expr_id)
            else:
                logging.error(f"[IMPLIES Unsupported antecedent op={ante.op}, expr={expr}]")
                sys.exit(1)

        else:
            logging.error(f"[IMPLIES Unsupported antecedent op={ante.op}, expr={expr}]")
            sys.exit(1)

    def choose_key_var(self, lhs: ExprNode, rhs: ExprNode) -> Optional[str]:
        """
        Heuristic: Prefer to use variable as dict key.
        """
        if isinstance(lhs, ExprNode) and is_var(lhs):
            return lhs.args[0]
        if isinstance(rhs, ExprNode) and is_var(rhs):
            return rhs.args[0]
        return None

    def is_equality_or_inequality(self, expr: Union[ExprNode, str]) -> bool:
        """
        Recursively check whether the expression or any subexpression is an equality or inequality.
        Supports: =, >, <, >=, <=, not (with one args)
        """
        if not isinstance(expr, ExprNode):
            return False
    
        if expr.op in {"ite", "=>"}:
            return False
        elif expr.op in {"=", ">", "<", ">=", "<="} and len(expr.args) == 2:
            return True
        elif expr.op == "var":
            return True 
        elif expr.op == "not" and len(expr.args) == 1:
            inner = expr.args[0]
            if isinstance(inner, ExprNode) and inner.op == "var":
                return True
    
        for arg in expr.args:
            if isinstance(arg, ExprNode) and not self.is_equality_or_inequality(arg):
                return False
            elif isinstance(arg, ExprNode) and self.is_equality_or_inequality(arg):
                return True
    
        return False 
    
    def extract_equal_exprs(self, expr: ExprNode) -> Dict[str, List[ExprNode]]:
        equal_exprs = {}
    
        def recurse(e: Union[ExprNode, str]):
            if not isinstance(e, ExprNode):
                return
            if e.op == "=" and len(e.args) == 2:
                lhs, rhs = e.args
                key_var = self.choose_key_var(lhs, rhs)
                if key_var:
                    equal_exprs.setdefault(key_var, []).append(e)
            elif e.op == "var":
                var_name = e.args[0]
                equal_exprs.setdefault(var_name, []).append(
                    ExprNode("=", [e, make_const("true")])
                )
            elif e.op == "not" and len(e.args) == 1:
                arg = e.args[0]
                if is_var(arg):
                    # 把 not (var x) 当作等式 x = false
                    var_name = arg.args[0]
                    equal_exprs.setdefault(var_name, []).append(
                        ExprNode("=", [arg, make_const("false")])
                    )
                else:
                    print("ERROR")
                    sys.exit(1)
            elif e.op in {"and", "or"}:
                for sub in e.args:
                    recurse(sub)
            else:
                for arg in e.args:
                    recurse(arg)
    
        recurse(expr)
        return equal_exprs
    
    def extract_inequal_exprs(self, expr: ExprNode) -> Dict[str, List[ExprNode]]:
        inequal_exprs = {}
        inequal_ops = {">", "<", ">=", "<="}
    
        def recurse(e: Union[ExprNode, str]):
            if not isinstance(e, ExprNode):
                return
    
            if e.op in inequal_ops and len(e.args) == 2:
                lhs, rhs = e.args
                key_var = self.choose_key_var(lhs, rhs)
                if key_var:
                    inequal_exprs.setdefault(key_var, []).append(e)
            elif e.op == "not" and len(e.args) == 1:
                pass
            elif e.op in {"and", "or"}:
                for sub in e.args:
                    recurse(sub)
            else:
                for arg in e.args:
                    recurse(arg)
    
        recurse(expr)
        return inequal_exprs

    def get_condnodes(self):
        temp_cond_nodes = self.cond_nodes
        # self.cond_nodes = []
        return temp_cond_nodes

    
def collect_vars_from_expr(expr) -> Set[str]:
    """递归提取ExprNode中所有变量名"""
    vars_found = set()
    def recurse(e):
        if not isinstance(e, ExprNode):
            return
        if e.op == "var":
            vars_found.add(e.args[0])
        else:
            for arg in e.args:
                recurse(arg)
    recurse(expr)
    return vars_found

def build_condnode_dependency_graph(condnodes: List[CondNode]) -> Dict[int, Set[int]]:
    # 1. 建立变量名 -> CondNode索引 映射
    var_to_node = {}
    for idx, node in enumerate(condnodes):
        for v in node.equal_exprs.keys():
            var_to_node[v] = idx
        for v in node.inequal_exprs.keys():
            var_to_node[v] = idx

    # 2. 建立图（邻接表）
    graph = {i: set() for i in range(len(condnodes))}

    # 3. 对每个 CondNode，提取 cond_expr 里的变量
    for i, node in enumerate(condnodes):
        if node.cond_expr is None:
            continue
        vars_in_cond = collect_vars_from_expr(node.cond_expr)
        for v in vars_in_cond:
            if v in var_to_node:
                j = var_to_node[v]
                if j != i:
                    graph[j].add(i)  # j -> i
    # 中间打印依赖图，格式：节点号 -> 依赖节点列表
    print("Dependency graph:")
    for k in sorted(graph.keys()):
        print(condnodes[k])
        print(f"  Node {k} -> {sorted(graph[k])}")
        print("------------------------------------------------------------------------------------")

    return graph

def detect_cycle(graph: Dict[int, Set[int]]) -> bool:
    visited = set()
    rec_stack = set()

    def dfs(node: int) -> bool:
        if node in rec_stack:
            return True  # cycle detected
        if node in visited:
            return False

        visited.add(node)
        rec_stack.add(node)
        for neighbor in graph.get(node, set()):
            if dfs(neighbor):
                return True
        rec_stack.remove(node)
        return False

    for node in graph:
        if node not in visited:
            if dfs(node):
                return True

    return False


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python exprnode.py /your/path/to/work/directory")
        exit(1)

    path = sys.argv[1]
    smt_encoding_file = os.path.join(path, 'inlined_smt_encoding_test.smt2')

    with open(smt_encoding_file, 'r', encoding='utf-8') as f:
        smt_encoding = f.read()
        smt_lines = smt_encoding.splitlines()


    expr_extractor = ExprNodeExtractor()
    expr_extractor.parse(smt_lines)
    exprnodes = expr_extractor.get_exprnodes()

    expr_id = 1
    cond_extractor = CondNodeExtractor()
    for exprnode in exprnodes:
        cond_extractor.handle_top_level(exprnode, expr_id)
        expr_id = expr_id + 1
        # print(exprnode)
        # for condnode in cond_extractor.get_condnodes():
        #     print(condnode)
        # print("------------------------------------------------------------------------------------")

    condnodes = cond_extractor.get_condnodes()

    # 使用示例
    dep_graph = build_condnode_dependency_graph(condnodes)
    if detect_cycle(dep_graph):
        print("有环，存在循环依赖")
    else:
        print("无环，依赖关系合法")
