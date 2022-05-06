#import spot
from formula import formula as spot
from operators import op
import altautomaton as alt

class Ltl2Alt:
    init_formula = None
    automaton = None

    def __init__(self):
        self.automaton = alt.Automaton()

    def is_original(self, f):
        if f._is(op.ff) or f._is(op.tt) or f._is(op.ap) or f._is(op.X) or f._is(op.Not):
            return True
        else:
            return False

    # Relies on negation normal form!
    def helper(self,source):
        #formula = source.get_label()
        formula = spot.formula(source.get_label())
        if formula._is(op.ap) or formula._is(op.tt) or formula._is(op.ff):
            return
        if formula._is(op.Not):
            return
        if formula._is(op.And):
            child_list = []
            for child in formula:
                new_node = alt.Node(child, self.is_original(child), False, False)
                self.automaton.add_node(new_node)
                child_list.append(new_node)
                self.helper(new_node)
            self.automaton.create_edge(source, child_list)
            self.automaton.create_formula_edge(source, child_list)
        if formula._is(op.Or):
            for child in formula:
                new_node = alt.Node(child, self.is_original(child), False, False)
                self.automaton.add_node(new_node)
                self.helper(new_node)
                self.automaton.create_edge(source, [new_node])
                self.automaton.create_formula_edge(source, [new_node])
        if formula._is(op.X):
            child = formula[0]
            new_node = alt.Node(child, self.is_original(child), False, False)
            self.automaton.add_node(new_node)
            self.helper(new_node)
            self.automaton.create_edge(source, [new_node])
            self.automaton.create_formula_edge(source, [new_node])
        if formula._is(op.U):
            phi = formula[0]
            psi = formula[1]
            true = spot.tt()
            phi_node = alt.Node(phi, self.is_original(phi), False, False)
            psi_node = alt.Node(psi, self.is_original(psi), False, False)
            true_node = alt.Node(true, self.is_original(true), False, False)
            new_and = spot.And([phi, spot.ap("true")]) #spot simplifies
            new_and_node = alt.Node(new_and, self.is_original(new_and), False, False)
            self.automaton.add_node(phi_node)
            self.automaton.add_node(psi_node)
            self.automaton.add_node(true_node)
            self.automaton.add_node(new_and_node)
            self.automaton.create_edge(source, [psi_node])
            self.automaton.create_formula_edge(source, [psi_node])
            self.automaton.create_edge(source, [new_and_node])
            self.automaton.create_edge(new_and_node, [phi_node, true_node])
            self.automaton.create_formula_edge(source, [phi_node])
            self.automaton.create_edge(true_node, [source])
            self.helper(phi_node)
            self.helper(psi_node)
        if formula._is(op.W):
            phi = formula[0]
            psi = formula[1]
            true = spot.tt()
            phi_node = alt.Node(phi, self.is_original(phi), False, False)
            psi_node = alt.Node(psi, self.is_original(psi), False, False)
            true_node = alt.Node(true, self.is_original(true), False, True)#difference to Until
            new_and = spot.And([phi, spot.ap("true")]) #spot simplifies
            new_and_node = alt.Node(new_and, self.is_original(new_and), False, False)
            self.automaton.add_node(phi_node)
            self.automaton.add_node(psi_node)
            self.automaton.add_node(true_node)
            self.automaton.add_node(new_and_node)
            self.automaton.create_edge(source, [psi_node])
            self.automaton.create_formula_edge(source, [psi_node])
            self.automaton.create_edge(source, [new_and_node])
            self.automaton.create_edge(new_and_node, [phi_node, true_node])
            self.automaton.create_formula_edge(source, [phi_node])
            self.automaton.create_edge(true_node, [source])
            self.helper(phi_node)
            self.helper(psi_node)
        if formula._is(op.R):
            phi = formula[0]
            psi = formula[1]
            true = spot.tt()
            phi_node = alt.Node(phi, self.is_original(phi), False, False)
            psi_node = alt.Node(psi, self.is_original(psi), False, False)
            true_node = alt.Node(true, self.is_original(true), False, True)
            new_and = spot.And([psi, spot.ap("true")]) #spot simplifies, therefore  spot.formula.ap("true") before
            new_and_node = alt.Node(new_and, self.is_original(new_and), False, False)
            second_and = spot.And([phi,psi])
            second_and_node = alt.Node(second_and, self.is_original(new_and), False, False)
            self.helper(phi_node)
            self.helper(psi_node)
            self.automaton.add_node(phi_node)
            self.automaton.add_node(psi_node)
            self.automaton.add_node(true_node)
            self.automaton.add_node(new_and_node)
            self.automaton.add_node(second_and_node)
            self.automaton.create_edge(source, [new_and_node])
            self.automaton.create_edge(source, [second_and_node])
            self.automaton.create_edge(new_and_node, [psi_node, true_node])
            self.automaton.create_formula_edge(source, [phi_node])
            self.automaton.create_edge(second_and_node, [phi_node, psi_node])#was phi2
            self.automaton.create_formula_edge(source, [psi_node])
            self.automaton.create_edge(true_node, [source])

            #self.helper(phi2_node)
        if formula._is(op.G):
            phi = formula[0]
            true = spot.tt()
            phi_node = alt.Node(phi, self.is_original(phi), False, False)
            true_node = alt.Node(true, self.is_original(true), False, True)
            self.automaton.add_node(phi_node)
            self.automaton.add_node(true_node)
            self.automaton.create_edge(source, [phi_node, true_node])
            self.automaton.create_formula_edge(source, [phi_node])
            #self.automaton.create_edge(source, [true_node])
            self.automaton.create_edge(true_node, [source])
            self.helper(phi_node)
        if formula._is(op.F):
            phi = formula[0]
            true = spot.tt()
            phi_node = alt.Node(phi, self.is_original(phi), False, False)
            true_node = alt.Node(true, self.is_original(true), False, False)
            self.automaton.add_node(phi_node)
            self.automaton.add_node(true_node)
            self.automaton.create_edge(source, [phi_node])
            self.automaton.create_formula_edge(source, [phi_node])
            self.automaton.create_edge(source, [true_node])
            self.automaton.create_edge(true_node, [source])
            self.helper(phi_node)
        return

    def transform(self, f):
        self.init_fomula = f
        init_node = alt.Node(f, self.is_original(f), True, False)
        self.automaton.add_node(init_node)
        self.helper(init_node)
        for n in self.automaton.nodes:
            if isinstance(n.label, str):
                exit(n.label)
        self.automaton.nodes.sort(key=lambda x: len(x.label.to_str().replace("true", "").replace("&", "").replace("|", "")), reverse=True)
        return self.automaton


