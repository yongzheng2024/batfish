class CondNode:
    def __init__(self, conditions: map, equalities: map, branch_type: bool):
        self.conditions = conditions
        self.equalities = equalities
        self.branch_type = branch_type

    def can_parse(self):
        # TODO

    def is_valid(self):
        # TODO
