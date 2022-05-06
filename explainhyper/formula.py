import spot
import sys
import argparse
#import translator

from operators import op


class formula:

    operator = None
    operands = None

    def __init__(self, operator, operands):
        self.operator = operator
        self.operands = operands
    def __eq__(self, other):
        if self.operator != other.operator:
            return False
        if len(self.operands) != len(other.operands):
            return False
        for op in self.operands:
            for op2 in other.operands:
                if op != op2:
                    return False
        return True
    def __hash__(self):
        return hash(self.operator) + len(self.operands)

    def __getitem__(self, key):
        return self.operands[key]
    def __setitem__(self, key, value):
        self.operands[key] = value
    def __iter__(self):
        return self.operands.__iter__()

    def _is(self, op):
        return self.operator is op

    def ap(string):
        return formula(op.ap, [string])
    def And(list_operands):
        return formula(op.And, list_operands)
    def Or(list_operands):
        return formula(op.Or, list_operands)
    def ap(operand):
        return formula(op.ap, [operand])
    def Not(operand):
        return formula(op.Not, [operand])
    def tt():
        return formula(op.tt, [])
    def ff():
        return formula(op.ff, [])
    def X(operand):
        return formula(op.X, [operand])
    def G(operand):
        return formula(op.G, [operand])
    def F(operand):
        return formula(op.F, [operand])
    def U(operand1, operand2):
        return formula(op.U, [operand1, operand2])
    def R(operand1, operand2):
        return formula(op.R, [operand1, operand2])
    def W(operand1, operand2):
        return formula(op.W, [operand1, operand2])
    def Implies(operand1, operand2):
        return formula(op.Implies, [operand1, operand2])
    def Equiv(operand1, operand2):
        return formula(op.Equiv, [operand1, operand2])
    def nImplies(operand1, operand2):
        return formula(op.nImplies, [operand1, operand2])
    def nEquiv(operand1, operand2):
        return formula(op.nEquiv, [operand1, operand2])


    #this formula cosntructs a formula from a string or a formula in spot format!
    def formula_from_spot(input):
        f = input
        if isinstance(input, str):
            f = spot.formula(input)
        if f._is(spot.op_ap):
            return formula.ap(f.to_str())
        if f._is(spot.op_Not):
            return formula.Not(formula.formula_from_spot(f[0]))
        if f._is(spot.op_tt):
            return formula.tt()
        if f._is(spot.op_ff):
            return formula.ff()
        if f._is(spot.op_And):
            child_list = []
            for child in f:
                child_list.append(formula.formula_from_spot(child))
            return formula.And(child_list)
        if f._is(spot.op_Or):
            child_list = []
            for child in f:
                child_list.append(formula.formula_from_spot(child))
            return formula.Or(child_list)
        if f._is(spot.op_X):
            return formula.X(formula.formula_from_spot(f[0]))
        if f._is(spot.op_U):
            a = formula.formula_from_spot(f[0])
            b = formula.formula_from_spot(f[1])
            return formula.U(a, b)
        if f._is(spot.op_R):
            a = formula.formula_from_spot(f[0])
            b = formula.formula_from_spot(f[1])
            return formula.R(a, b)
        if f._is(spot.op_Implies):
            a = formula.formula_from_spot(f[0])
            b = formula.formula_from_spot(f[1])
            return formula.Implies(a, b)
        if f._is(spot.op_Equiv):
            a = formula.formula_from_spot(f[0])
            b = formula.formula_from_spot(f[1])
            return formula.Equiv(a, b)
        if f._is(spot.op_G):
            return formula.G(formula.formula_from_spot(f[0]))
        if f._is(spot.op_F):
            return formula.F(formula.formula_from_spot(f[0]))

    def formula(input):
        f = input
        if isinstance(f, str):
            f = formula.formula_from_spot(f)
        if f._is(op.ap):
            return formula.ap(f.to_str())
        if f._is(op.Not):
            return formula.Not(formula.formula(f[0]))
        if f._is(op.tt):
            return formula.tt()
        if f._is(op.ff):
            return formula.ff()
        if f._is(op.And):
            child_list = []
            for child in f:
                child_list.append(formula.formula(child))
            return formula.And(child_list)
        if f._is(op.Or):
            child_list = []
            for child in f:
                child_list.append(formula.formula(child))
            return formula.Or(child_list)
        if f._is(op.X):
            return formula.X(formula.formula(f[0]))
        if f._is(op.U):
            a = formula.formula(f[0])
            b = formula.formula(f[1])
            return formula.U(a, b)
        if f._is(op.R):
            a = formula.formula(f[0])
            b = formula.formula(f[1])
            return formula.R(a, b)
        if f._is(op.Implies):
            a = formula.formula(f[0])
            b = formula.formula(f[1])
            return formula.Implies(a, b)
        if f._is(op.Equiv):
            a = formula.formula(f[0])
            b = formula.formula(f[1])
            return formula.Equiv(a, b)
        if f._is(op.nImplies):
            a = formula.formula(f[0])
            b = formula.formula(f[1])
            return formula.nImplies(a, b)
        if f._is(op.nEquiv):
            a = formula.formula(f[0])
            b = formula.formula(f[1])
            return formula.nEquiv(a, b)
        if f._is(op.G):
            return formula.G(formula.formula(f[0]))
        if f._is(op.F):
            return formula.F(formula.formula(f[0]))


    def to_str(self):
        string = self.str()
        return (string)

    def str(self):
        if self.operator is op.ap:
            return self.operands[0]
        if self.operator is op.tt or self.operator is op.ff:
            return self.operator.to_str()
        if self.operator is op.G or self.operator is op.F or self.operator is op.X or self.operator is op.Not:
            string = self.operator.to_str()
            for child in self.operands:
                string = string + "(" + child.to_str() +")"
            return string
        if self.operator is op.And or self.operator is op.Or:
            string = ""
            i = 1
            for child in self.operands:
                string = string + "("
                string = string + child.to_str()
                string = string + ")"
                if i < len(self.operands):
                    string = string + self.operator.to_str()
                i = i + 1
            return string #+ ")"
        else:
            string = "(" + self.operands[0].to_str() + ")"
            string = string + self.operator.to_str()
            string = string + "(" + self.operands[1].to_str() + ")"
            return string

    def to_str_lbt(self):
        string = self.str_lbt()
        return (string)


    def str_lbt(self):
        if self.operator is op.ap:
            string = "AP"
            trace_assignment = self.operands[0].rsplit("_",1)
            string = string + " \"" + trace_assignment[0] + "\" " + trace_assignment[1]
            return string
        else:
            string = self.operator.to_str_lbt()
            for child in self.operands:
                string = string + " (" + child.to_str_lbt() + ")"
            return string



if __name__ == "__main__":
    p = argparse.ArgumentParser(description='spot to mchyper')
    # flags
    p.add_argument('-f', help='The formula in spot format')
    args = p.parse_args()
    f = spot.formula(args.f)
    f = formula.formula_from_spot(f)
    print(f.to_str_lbt())


