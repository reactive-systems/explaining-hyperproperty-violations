#import spot
import formula as spot
import sys
import altautomaton
import re
from operators import op
class Translator:

    def negate(formula, check = False):
        if not check:
            f = spot.negative_normal_form(formula)
        else:
            f = formula
        f = Translator.help_negate(f)
        return f

    def help_negate(formula):
        #formula = spot.formula.formula(formula)
        if formula._is(op.ap):
            return spot.formula.Not(formula)
        if formula._is(op.Not):
            return formula[0]
        if formula._is(op.tt):
            return op.ff
        if formula._is(op.ff):
            return op.tt
        if formula._is(op.And):
            child_list = []
            for child in formula:
                child_list.append(Translator.help_negate(child))
            return spot.formula.Or(child_list)
        if formula._is(op.Or):
            child_list = []
            for child in formula:
                child_list.append(Translator.help_negate(child))
            return spot.formula.And(child_list)
        if formula._is(op.X):
            return spot.formula.X(Translator.help_negate(formula[0]))
        if formula._is(op.U):
            a = Translator.help_negate(formula[0])
            b = Translator.help_negate(formula[1])
            return spot.formula.R(a, b)
        if formula._is(op.R):
            a = Translator.help_negate(formula[0])
            b = Translator.help_negate(formula[1])
            return spot.formula.U(a,b)
        if formula._is(op.G):
            a = Translator.help_negate(formula[0])
            return spot.formula.F(a)
        if formula._is(op.F):
            a = Translator.help_negate(formula[0])
            return spot.formula.G(a)
        else:
            print("This state should not be reached in help_negate original")
            print(formula.to_str())
            sys.exit()


    def negate_output_list(automaton):
        for node in automaton.get_nodes():
            negation_result = Translator.negate(spot.formula(node.get_label()))
            if negation_result is 0:
                negation_result = spot.formula.ff()
            if negation_result is 1:
                negation_result = spot.formula.tt()
            node.label = spot.formula(negation_result).to_str()
            #This would negate all values also, but loses explanation for formulas
            #for i in range(len(node.result_array)):
             #   node.set_result_at(i, spot.formula.Not(node.get_result_at(i)))
        return automaton

    # filter out spot syntax, use function on formula in AP case and on traces array in preprocess 
    def filter_out_spot_syntax_from_APs(formula):
        formula = formula.replace("|", "")
        formula = formula.replace("<", "")
        formula = formula.replace(">", "")
        formula = formula.replace("[", "")
        formula = formula.replace("]", "")
        formula = formula.replace("*", "")
        formula = formula.replace("!", "")
        formula = formula.replace("&", "")
        formula = formula.replace("G", "g")
        formula = formula.replace("F", "f")
        formula = formula.replace("U", "u")
        formula = formula.replace("W", "w")
        formula = formula.replace("R", "r")
        return formula

    # iterate over all inputs and require all that are not in the exception list to be equivalent on both traces
    def handle_SameInputsExcept(id1, id2, exception_list, circuit): # SameInputsExcept Int Int [String]
        formula = " t " 
        if (exception_list == None):
            exception_list = ''
        exception_list = re.sub(' ', '', exception_list)
        exceptions = exception_list.split(',')
        for input_ap in sorted(list(circuit.inputs)):
            if (('"' + input_ap + '"' not in exceptions)):
                ap = Translator.filter_out_spot_syntax_from_APs(input_ap)
                formula = " & " + formula + " e " + ap + "_" + id1 + " " + ap + "_" + id2 + " "
        return formula

    # require all APs (inputs, latches and outputs) from the AP list to be equivalent on both traces
    def handle_EqualOn(id1, id2, AP_list, circuit): # EqualOn Int Int [String]
        formula = " t "
        if (AP_list == None):
            AP_list = ''
        AP_list = re.sub(' ', '', AP_list)
        APs = AP_list.split(',')
        for ap in APs: 
            ap = ap[1:-1]
            if ((ap in circuit.inputs) | (ap in circuit.latches) | (ap in circuit.outputs)):
                ap = Translator.filter_out_spot_syntax_from_APs(ap)
                formula = " & " + formula + " e " + ap + "_" + id1 + " " + ap + "_" + id2 + " "
        return formula

    # require all latches to be equivalent on both traces 
    def handle_SameState(id1, id2, circuit): # SameState Int Int
        formula = " t "
        for ap in sorted(list(circuit.latches)): 
            ap = Translator.filter_out_spot_syntax_from_APs(ap)
            formula = " & " + formula + " e " + ap + "_" + id1 + " " + ap + "_" + id2 + " "
        return formula

    def mchyper_to_spot(formula, circuit):
        negate = False
        if (re.match(r"^Forall", formula)):
            negate = True

        # delete quantifiers to end up with an LTL formula
        formula = formula.replace("Forall", "")
        formula = formula.replace("Exists", "")
        # 
        formula = formula.replace("Const True", "1")
        formula = formula.replace("Const False", "0")
        # replace arbitrary whitespaces by a single space
        formula = re.sub(r'[ \t\n\r\f\v]+', ' ', formula)
        
        # handle special derived operators
        # unroll formulas of the form 'SameInputsExcept <trace_id> <trace_id> <list of comma separated inputs to ignore, possibly empty>' (and translate to spot syntax) 
        formula = re.sub(r'SameInputsExcept\s+?([0-9]+?)\s+?([0-9]+?)\s+?\[((,? ?"[^":@=]+")+?)?]', lambda match: Translator.handle_SameInputsExcept(match.group(1), match.group(2), match.group(3), circuit), formula) 
        # unroll formulas of the form 'EqualOn <trace_id> <trace_id> <list of comma separated atomic propositions to require equality>' (and translate to spot syntax) 
        formula = re.sub(r'EqualOn\s+?([0-9]+?)\s+?([0-9]+?)\s+?\[((,? ?"[^":@=]+")+?)?]', lambda match: Translator.handle_EqualOn(match.group(1), match.group(2), match.group(3), circuit), formula) 
        # unroll formulas of the form 'SameState <trace_id> <trace_id>' (and translate to spot syntax) 
        formula = re.sub(r'SameState\s+?([0-9]+?)\s+?([0-9]+?)', lambda match: Translator.handle_SameState(match.group(1), match.group(2), circuit), formula) 

        # handle atomic propositions: transform 'AP "<name>" <trace_id>' to '<name>_<trace_id>'
        formula = re.sub(r"AP\s+?\"([^:@=]+?)\"\s+?([0-9]+?)", lambda match: Translator.filter_out_spot_syntax_from_APs(match.group(1)) + "_" + match.group(2), formula) 
        # replace boolean and temporal operators with corresponding spot operators
        formula = formula.replace("Neg", "!")
        formula = formula.replace("And", "&")
        formula = formula.replace("Or", "|")
        formula = formula.replace("Implies", "i")
        formula = formula.replace("Eq", "e")
        formula = formula.replace("Neq", "! e")
        # formula = formula.replace("X", "X")
        formula = formula.replace("Until", "U")
        # formula = formula.replace("G", "G")
        # formula = formula.replace("F", "F")
        formula = formula.replace("Release", "R")
        formula = formula.replace("WUntil", "W")
        formula = formula.replace("(", " ")
        formula = formula.replace(")", " ")
        return (negate, formula)

    def formula_without_syntactic_sugar(f):
        f = spot.formula.formula(f)
        if f._is(op.ap) or f._is(op.tt) or f._is(op.ff):
            return f
        if f._is(op.Not):
            return spot.formula.Not(Translator.formula_without_syntactic_sugar(f[0]))
        if f._is(op.Implies):
            childlist = []
            childlist.append(Translator.formula_without_syntactic_sugar(spot.formula.Not(f[0])))
            childlist.append(Translator.formula_without_syntactic_sugar(f[1]))
            return spot.formula.Or(childlist)
        if f._is(op.Equiv):
            and1 = []
            and2 = []
            and1.append(Translator.formula_without_syntactic_sugar(f[0]))
            and1.append(Translator.formula_without_syntactic_sugar(f[1]))
            and2.append(Translator.formula_without_syntactic_sugar(spot.formula.Not(f[0])))
            and2.append(Translator.formula_without_syntactic_sugar(spot.formula.Not(f[1])))
            and1f = spot.formula.And(and1)
            and2f = spot.formula.And(and2)
            orf = spot.formula.Or([and1f, and2f])
            return orf
        if f._is(op.nImplies):
            childlist = []
            childlist.append(Translator.formula_without_syntactic_sugar(f[0]))
            childlist.append(Translator.formula_without_syntactic_sugar(spot.formula.Not(f[1])))
            return spot.formula.And(childlist)
        if f._is(op.nEquiv):
            and1 = []
            and2 = []
            and1.append(Translator.formula_without_syntactic_sugar(f[0]))
            and1.append(Translator.formula_without_syntactic_sugar(f[1]))
            and2.append(Translator.formula_without_syntactic_sugar(spot.formula.Not(f[0])))
            and2.append(Translator.formula_without_syntactic_sugar(spot.formula.Not(f[1])))
            and1f = spot.formula.Or(and1)
            and2f = spot.formula.Or(and2)
            orf = spot.formula.And([and2f, and1f])
            return orf
        if f._is(op.And):
            child_list = []
            for child in f:
                child_list.append(Translator.formula_without_syntactic_sugar(child))
            return spot.formula.And(child_list)
        if f._is(op.Or):
            child_list = []
            for child in f:
                child_list.append(Translator.formula_without_syntactic_sugar(child))
            return spot.formula.Or(child_list)
        if f._is(op.X):
            return spot.formula.X(Translator.formula_without_syntactic_sugar(f[0]))
        if f._is(op.U):
            a = Translator.formula_without_syntactic_sugar(f[0])
            b = Translator.formula_without_syntactic_sugar(f[1])
            return spot.formula.U(a, b)
        if f._is(op.R):
            a = Translator.formula_without_syntactic_sugar(f[0])
            b = Translator.formula_without_syntactic_sugar(f[1])
            return spot.formula.R(a,b)
        if f._is(op.G):
            a = Translator.formula_without_syntactic_sugar(f[0])
            return spot.formula.G(a)
        if f._is(op.F):
            a = Translator.formula_without_syntactic_sugar(f[0])
            return spot.formula.F(a)
        else:
            print("This state should not be reached.")
            print(f.to_str())
            sys.exit()


    def negative_normal_form(formula):
        #formula = spot.formula.formula(formula)
        if formula._is(op.ap) or formula._is(op.tt) or formula._is(op.ff):
            return formula
        if formula._is(op.Not):
            if formula[0]._is(op.ap):
                return formula
            else:
                return Translator.negative_normal_form(Translator.negate(formula[0], True))
        if formula._is(op.And):
            child_list = []
            for child in formula:
                child_list.append(Translator.negative_normal_form(child))
            return spot.formula.And(child_list)
        if formula._is(op.Or):
            child_list = []
            for child in formula:
                child_list.append(spot.formula.formula(Translator.negative_normal_form(child)))
            return spot.formula.Or(child_list)
        if formula._is(op.X):
            return spot.formula.X(Translator.negative_normal_form(formula[0]))
        if formula._is(op.U):
            a = Translator.negative_normal_form(formula[0])
            b = Translator.negative_normal_form(formula[1])
            return spot.formula.U(a, b)
        if formula._is(op.R):
            a = Translator.negative_normal_form(formula[0])
            b = Translator.negative_normal_form(formula[1])
            return spot.formula.R(a, b)
        if formula._is(op.G):
            a = Translator.negative_normal_form(formula[0])
            return spot.formula.G(a)
        if formula._is(op.F):
            a = Translator.negative_normal_form(formula[0])
            return spot.formula.F(a)
        else:
            print("This state should not be reached.")
            print(formula.to_str())
            sys.exit()

    def negate_enf(formula, check = False):
        if not check:
            f = spot.negative_normal_form(formula)
        else:
            f = formula
        f = Translator.help_negate_enf(f)
        return f

    def help_negate_enf(formula):
        #formula = spot.formula.formula(formula)
        if formula._is(op.ap):
            return spot.formula.Not(formula)
        if formula._is(op.Not):
            return formula[0]
        if formula._is(op.tt):
            return op.ff
        if formula._is(op.ff):
            return op.tt
        if formula._is(op.And):
            child_list = []
            for child in formula:
                child_list.append(Translator.help_negate_enf(child))
            return spot.formula.Or(child_list)
        if formula._is(op.Or):
            child_list = []
            for child in formula:
                child_list.append(Translator.help_negate_enf(child))
            return spot.formula.And(child_list)
        if formula._is(op.X):
            return spot.formula.X(Translator.help_negate_enf(formula[0]))
        if formula._is(op.U):
            a = Translator.help_negate_enf(formula[0])
            b = Translator.help_negate_enf(formula[1])
            return spot.formula.R(a, b)
        if formula._is(op.R):
            a = Translator.help_negate_enf(formula[0])
            b = Translator.help_negate_enf(formula[1])
            return spot.formula.U(a,b)
        if formula._is(op.G):
            a = Translator.help_negate_enf(formula[0])
            return spot.formula.F(a)
        if formula._is(op.F):
            a = Translator.help_negate_enf(formula[0])
            return spot.formula.G(a)
        if formula._is(op.Equiv):
            return spot.formula.nEquiv(formula[0],formula[1])
        if formula._is(op.nEquiv):
            return spot.formula.Equiv(formula[0], formula[1])
        if formula._is(op.Implies):
            return spot.formula.nImplies(formula[0],formula[1])
        if formula._is(op.nImplies):
            return spot.formula.Implies(formula[0], formula[1])

        else:
            print("This state should not be reached in help_negate_enf")
            print(formula.to_str())
            sys.exit()

    def equivalence_normal_form(formula):
        # formula = spot.formula.formula(formula)
        if formula._is(op.ap) or formula._is(op.tt) or formula._is(op.ff):
            return formula
        if formula._is(op.Not):
            if formula[0]._is(op.ap):
                return formula
            elif formula[0]._is(op.Equiv):
                a = Translator.equivalence_normal_form(formula[0][0])
                b = Translator.equivalence_normal_form(formula[0][1])
                return spot.formula.nEquiv(a, b)
            elif formula[0]._is(op.nEquiv):
                a = Translator.equivalence_normal_form(formula[0][0])
                b = Translator.equivalence_normal_form(formula[0][1])
                return spot.formula.Equiv(a, b)
            elif formula[0]._is(op.Implies):
                a = Translator.equivalence_normal_form(formula[0][0])
                b = Translator.equivalence_normal_form(formula[0][1])
                return spot.formula.nImplies(a, b)
            elif formula[0]._is(op.nImplies):
                a = Translator.equivalence_normal_form(formula[0][0])
                b = Translator.equivalence_normal_form(formula[0][1])
                return spot.formula.Implies(a, b)
            else:
                return Translator.equivalence_normal_form(Translator.negate_enf(formula[0], True))
        if formula._is(op.And):
            child_list = []
            for child in formula:
                child_list.append(Translator.equivalence_normal_form(child))
            return spot.formula.And(child_list)
        if formula._is(op.Or):
            child_list = []
            for child in formula:
                child_list.append(spot.formula.formula(Translator.equivalence_normal_form(child)))
            return spot.formula.Or(child_list)
        if formula._is(op.X):
            return spot.formula.X(Translator.equivalence_normal_form(formula[0]))
        if formula._is(op.U):
            a = Translator.equivalence_normal_form(formula[0])
            b = Translator.equivalence_normal_form(formula[1])
            return spot.formula.U(a, b)
        if formula._is(op.R):
            a = Translator.equivalence_normal_form(formula[0])
            b = Translator.equivalence_normal_form(formula[1])
            return spot.formula.R(a, b)
        if formula._is(op.G):
            a = Translator.equivalence_normal_form(formula[0])
            return spot.formula.G(a)
        if formula._is(op.F):
            a = Translator.equivalence_normal_form(formula[0])
            return spot.formula.F(a)
        if formula._is(op.Equiv):
            a = Translator.equivalence_normal_form(formula[0])
            b = Translator.equivalence_normal_form(formula[1])
            return spot.formula.Equiv(a,b)
        if formula._is(op.nEquiv):
            a = Translator.equivalence_normal_form(formula[0])
            b = Translator.equivalence_normal_form(formula[1])
            return spot.formula.nEquiv(a, b)
        if formula._is(op.Implies):
            a = Translator.equivalence_normal_form(formula[0])
            b = Translator.equivalence_normal_form(formula[1])
            return spot.formula.Implies(a, b)
        if formula._is(op.nImplies):
            a = Translator.equivalence_normal_form(formula[0])
            b = Translator.equivalence_normal_form(formula[1])
            return spot.formula.nImplies(a,b)
        else:
            print("This state should not be reached.")
            print(formula.to_str())
            sys.exit()

    def ap_list_to_trace(list, symbol):
        trace = []
        for timestep in range(len(list)):
            current_word = []
            for word in list[timestep]:
                if list[timestep][word] == 1:
                    current_word.append(word+"_"+symbol)
            trace.append(current_word)
        return trace
