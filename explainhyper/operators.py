from enum import Enum

class op(Enum):
    ap = ["",""]
    Not = ["!","Neg"]
    tt = ["1", "Const True"]
    ff = ["0", "Const False"]
    X = ["X", "X"]
    G = ["G", "G"]
    F = ["F", "F"]
    U = ["U", "Until"]
    R = ["R", "Release"]
    W = ["W", "WUntil"]
    Implies = ["->", "Implies"]
    nImplies = ["!->", "Nimplies"]
    Equiv = ["<->", "Eq"]
    nEquiv = ["<!->", "Neq"]
    And = ["&", "And"]
    Or = ["|", "Or"]

    def to_str(self):
        return self.value[0]
    def to_str_lbt(self):
        return self.value[1]