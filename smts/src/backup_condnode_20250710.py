
from typing import List, Dict, Union, Optional

class ExprNode:
    def __init__(self, op: str, args: List[Union['ExprNode', str]]):
        self.op = op
        self.args = args

    def __repr__(self):
        return f"({self.op} {' '.join(str(a) for a in self.args)})"

class CondNode:
    def __init__(
        self,
        cond_expr: Union[ExprNode, str],
        equal_exprs: Dict[str, ExprNode],
        expr_id: int,
        inequality_exprs: Optional[List[ExprNode]] = None,
        inherited_equal_exprs: Optional[Dict[str, ExprNode]] = None,
        inherited_inequalities: Optional[List[ExprNode]] = None,
    ):
        self.cond_expr = cond_expr
        self.equal_exprs = equal_exprs
        self.expr_id = expr_id

        self.inequality_exprs = inequality_exprs or []
        self.inherited_equal_exprs = inherited_equal_exprs or {}
        self.inherited_inequalities = inherited_inequalities or []

    def __repr__(self):
        return (
            f"CondNode(cond_expr={self.cond_expr}, "
            f"equal_exprs={self.equal_exprs}, "
            f"expr_id={self.expr_id})"
        )

class CondNodeExtractor:
    def __init__(self):
        self.cond_nodes: List[CondNode] = []

    def parse_all(self, exprs: List[ExprNode]) -> List[CondNode]:
        for idx, expr in enumerate(exprs):
            self.handle_ite_recursive(expr, expr_id=idx, prefix_cond=[])
        return self.cond_nodes

    def extract_equal_exprs(self, expr: Union[ExprNode, str]) -> Dict[str, ExprNode]:
        result = {}
        if isinstance(expr, str):
            result[expr] = make_const("true")
            return result
        if expr.op == "and":
            for arg in expr.args:
                result.update(self.extract_equal_exprs(arg))
        elif expr.op == "=":
            lhs, rhs = expr.args
            if isinstance(lhs, str):
                result[lhs] = rhs
        elif expr.op == "not":
            sub = expr.args[0]
            if isinstance(sub, str):
                result[sub] = make_const("false")
        return result

    def handle_ite_recursive(self, expr: ExprNode, expr_id: int, prefix_cond: List[ExprNode]):
        if expr.op != "ite":
            return
        cond_expr, then_expr, else_expr = expr.args

        if cond_expr.op == "and":
            # generate individual false conditions for each conjunct
            for subcond in cond_expr.args:
                self.cond_nodes.append(
                    CondNode(
                        cond_expr=subcond,
                        equal_exprs=self.extract_equal_exprs(else_expr),
                        expr_id=expr_id,
                    )
                )
            # do not add the full (not (and ...)) path to avoid redundancy
            new_prefix = prefix_cond + cond_expr.args
            self.handle_branch_with_nested_ite(
                cond_expr=ExprNode("and", new_prefix),
                branch_expr=then_expr,
                expr_id=expr_id,
            )
            return

        if cond_expr.op == "or":
            for subcond in cond_expr.args:
                self.cond_nodes.append(
                    CondNode(
                        cond_expr=ExprNode("and", prefix_cond + [subcond]),
                        equal_exprs=self.extract_equal_exprs(then_expr),
                        expr_id=expr_id,
                    )
                )
            false_prefix = prefix_cond + [ExprNode("not", [cond_expr])]
            self.cond_nodes.append(
                CondNode(
                    cond_expr=ExprNode("and", false_prefix),
                    equal_exprs=self.extract_equal_exprs(else_expr),
                    expr_id=expr_id,
                )
            )
            return

        # general case: single condition
        self.cond_nodes.append(
            CondNode(
                cond_expr=ExprNode("and", prefix_cond + [cond_expr]),
                equal_exprs=self.extract_equal_exprs(then_expr),
                expr_id=expr_id,
            )
        )
        self.cond_nodes.append(
            CondNode(
                cond_expr=ExprNode("and", prefix_cond + [ExprNode("not", [cond_expr])]),
                equal_exprs=self.extract_equal_exprs(else_expr),
                expr_id=expr_id,
            )
        )

        # handle nested ite in branches recursively
        self.handle_branch_with_nested_ite(cond_expr, then_expr, expr_id)
        self.handle_branch_with_nested_ite(ExprNode("not", [cond_expr]), else_expr, expr_id)

    def handle_branch_with_nested_ite(self, cond_expr: ExprNode, branch_expr: Union[ExprNode, str], expr_id: int):
        if isinstance(branch_expr, ExprNode) and branch_expr.op == "ite":
            self.handle_ite_recursive(branch_expr, expr_id=expr_id, prefix_cond=[cond_expr])


if __name__ == "__main__":
    # test nested ite
    from exprnode import make_const, make_var

    expr = ExprNode("ite", [
        ExprNode("and", [
            ExprNode("=", ["x", make_const("1")]),
            ExprNode("=", ["y", make_const("2")])
        ]),
        ExprNode("ite", [
            ExprNode("or", [
                ExprNode("=", ["a", make_const("3")]),
                ExprNode("=", ["b", make_const("4")]),
            ]),
            ExprNode("=", ["z", make_const("10")]),
            ExprNode("=", ["z", make_const("11")]),
        ]),
        ExprNode("=", ["z", make_const("0")]),
    ])

    extractor = CondNodeExtractor()
    result = extractor.parse_all([expr])
    for r in result:
        print(r)
