import sys
from formula import formula as spot
from operators import op
import spot as spot_old
import altautomaton as alt
from translator import Translator
import trace
import output
import pygraphviz as viz
from satispy import CnfFromString
from pysat.solvers import Glucose4, Lingeling, Minisat22
from pysat.formula import CNF
import re

class Highlighter:
    aut = None
    trace = None


    def __init__(self, automaton, trace):
        self.aut = automaton
        self.trace = trace

    def run(self, orig_formula):
        for node in reversed(self.aut.get_nodes()):
            f = spot.formula(node.label)
            if node.is_original():
                if node.is_accepting() and self.trace.is_liveness():#TODO:EVALUATE FORMULA IF NOT TRUE
                    if self.is_true(int(node.get_label().to_str())):
                        node.set_array_at(self.trace.get_length()-1, spot.tt())
                if f._is(op.ap):
                    if f.to_str() in self.trace.value_at(self.trace.get_length()-1):
                        node.set_array_at(self.trace.get_length()-1, spot.tt())
                    else:
                        node.set_array_at(self.trace.get_length()-1, spot.ff())
        for i in range(self.trace.get_length()-1, -1, -1):
            for node in reversed(self.aut.get_nodes()):
                self.eval_orig(node, i)
            for node in reversed(self.aut.get_nodes()):
                self.eval_new(node, i)
        self.explanation_tree()




    def is_true(self, formula):
        if isinstance(formula, int):
            if formula == 0:
                return False
            if formula == 1:
                return True
        return spot_old.formula(formula.to_str())._is(spot_old.op_tt)

    def eval_orig(self, node, index):
        if node.get_result_at(index) != spot.ff():
            return
        if (node.is_original()):
            aps = self.trace.value_at(index)
            f = node.label
            nu = self.trace.value_at(index)
            if f._is(op.X) or f._is(op.tt) or f._is(op.ff): #This has the assumption of only one edge. always sat?
                node.set_array_at(index, node.get_outgoing_edges()[0].get_targets()[0].get_result_at(index + 1))
                if self.is_true(node.get_result_at(index)):
                    node.set_reason_at(index, {node.get_outgoing_edges()[0].get_targets()[0] : index+1})
            if f._is(op.ap):
                if f.to_str() in nu:
                    node.set_array_at(index,spot.tt())
                else:
                    node.set_array_at(index, spot.ff())
            if f._is(op.Not):
                if f[0].to_str() in nu:
                    node.set_array_at(index, spot.ff())
                else:
                    node.set_array_at(index, spot.tt())

    def eval_new(self, node, index):
        if not node.is_original():
            reason = []
            or_list = []
            for edge in node.get_outgoing_edges():
                and_list = []
                for target in edge.get_targets():
                    and_list.append(target.get_result_at(index))
                or_list.append(spot.And(and_list))
                if self.is_true(spot.And(and_list)):
                    reason.append(edge)
            node.set_array_at(index, spot.Or(or_list))
            if self.is_true(spot.Or(or_list)):
                reasons = {}
                #for x in reason:
                    #for n in x.get_targets():
                for n in reason[0].get_targets():
                        reasons[n] = index
                node.set_reason_at(index, reasons)

    def print_result_array(self):
        for node in self.aut.get_nodes():
            print("Node %s has values: %s" %(node.get_label().to_str(),node.result_array))
            for n in node.result_array:
                print(n.to_str())
            print("Node %s, %s has reasons: %s" % (node.get_label().to_str(), node, node.reason_array))


    def output_table_json(self):
        for n in self.aut.get_nodes():
            for i in range(len(n.result_array)):
                n.set_result_at(i, n.get_result_at(i).to_str())
        output.dump_json(self.aut)

    #Changes aut to deepcopy that is stripped to the explanation tree!!
    def explanation_tree(self):
        for node in self.aut.get_nodes():
            for i in range(self.trace.get_length()):
                node.set_array_at(i, 0)
        init = self.aut.get_init_node()
        self.explanation_tree_rec(init, 0)

    def explanation_tree_rec(self, node, at):
        node.set_array_at(at, 1)
        reason_dict = node.get_reason_at(at)
        for n, value in reason_dict.items():
           self.explanation_tree_rec(n, value)

    def formula_for_node(string):
        string = Translator.filter_out_spot_syntax_from_APs(string.replace(" ", ""))
        aplist = string.split(";")
        andlist = []
        for ap in aplist:
            value = ap.split("=")
            if ap:
                if value[1] == '0':
                    andlist.append(spot.formula("!" + value[0].replace('\'', '"')))
                else:
                    andlist.append(spot.formula(value[0].replace('\'', '"')))
        return spot.And(andlist)

    def state_eval(nu, f):
        f = spot_old.formula(f.to_str())
        if f._is(spot_old.op_tt) or f._is(spot_old.op_ff):
            return f
        if f._is(spot_old.op_ap):
            if f.to_str() in nu:
                return spot.tt()
            if f.to_str().replace("\"", "") in nu:
                return spot.tt()
            else:
                return spot.ff()
        if f._is(spot_old.op_And):
            list = []
            for child in f:
                list.append(Highlighter.state_eval(nu, child))
            return spot.And(list)
        if f._is(spot_old.op_Not):
            return spot.Not(Highlighter.state_eval(nu, f[0]))
        else:
            return f

    def dot_minimization(filename, trace, outName, all_aps):
        number_of_all_aps = len(list(all_aps[0])) + len(list(all_aps[1])) + len(list(all_aps[2]))
        print("Size of the counter example (|Gamma|) is: " + str(number_of_all_aps * trace.get_length()))

        in_graph = viz.AGraph(filename)
        out_graph = viz.AGraph(directed=True, strict=False)
        new_nodes = []
        new_edges = []
        node_formula_map = {}
        string_int_map = {}
        i = 0
        num_nodes = len(in_graph.nodes())

        #read the dot file with the lts
        for n in in_graph.nodes():
            formula = Highlighter.formula_for_node(n)
            node_formula_map[i] = formula
            out_graph.add_node(i, label=n.attr['label'])
            string_int_map[n] = i
            i = i + 1
        for e in in_graph.edges():
            newlist = []
            newlist.append(string_int_map[e[0]])
            newlist.append(string_int_map[e[1]])
            out_graph.add_edge(string_int_map[e[0]],string_int_map[e[1]], label=e.attr['label'])
            new_edges.append(tuple(newlist))
        with open(outName + ".dot", "w") as file:
           file.write(str(out_graph))

        #split the atomic propositions according to the traces
        tracemaps = [[] for n in range(2)]
        trace_0_dict = {}
        trace_1_dict = {}
        for k in range(trace.get_length()):
            trace0 = set()
            trace1 = set()
            current_values = trace.value_at(k)
            for ap in current_values:
                if ap.split("_")[len(ap.split("_"))-1] == "0":
                    trace0.add("_".join(ap.split("_")[:len(ap.split("_"))-1]))
                elif ap.split("_")[len(ap.split("_"))-1] == "1":
                    trace1.add("_".join(ap.split("_")[:len(ap.split("_"))-1]))
            test = False
            for j in range(num_nodes):
                if spot_old.formula(Highlighter.state_eval(trace0, node_formula_map[j]).to_str()) == spot_old.formula.tt().to_str():
                    tracemaps[0].append(j)
                    test = True
                    break
            if not test:
                t = ""
                for x in trace1:
                    t = t + x
                tracemaps[1].append(t)
            test = False
            for j in range(num_nodes):
                if spot_old.formula(Highlighter.state_eval(trace1, node_formula_map[j]).to_str()) == spot_old.formula.tt().to_str():
                    test = True
                    tracemaps[1].append(j)
                    break
            if not test:
                t = ""
                for x in trace1:
                    t = t + x
                tracemaps[1].append(t)
            trace_0_dict[k] = trace0
            trace_1_dict[k] = trace1
        #compute edgelists from nodes in tracemap
        edgelists = [[] for n in range(2)]
        edgelist_0 = []
        edgelist_1 = []
        for node_0, node_1, node_0_suc, node_1_suc in zip(tracemaps[0],tracemaps[1],tracemaps[0][1:],tracemaps[1][1:]):
            edgelist_0.append(out_graph.get_edge(node_0, node_0_suc))
            edgelist_1.append(out_graph.get_edge(node_1, node_1_suc))
        edgelists[0] = edgelist_0
        edgelists[1] = edgelist_1

        #build wp models via sat solving
        #filter for inputs
        input_aps = all_aps[0]
        trace_0_true_inputs = {}
        trace_0_false_inputs = {}
        trace_1_true_inputs = {}
        trace_1_false_inputs = {}
        for timestep in range(trace.get_length()):
            intersection_0 = trace_0_dict[timestep].intersection(input_aps)
            difference_0 = input_aps.difference(trace_0_dict[timestep])
            h_inter_0 = set()
            h_difference_0 = set()
            for l in intersection_0:
                h_inter_0.add(l+"#"+str(timestep))
            for l in difference_0:
                h_difference_0.add(l+"#"+str(timestep))
            trace_0_true_inputs[timestep] = h_inter_0
            trace_0_false_inputs[timestep] = h_difference_0
        
        for timestep in range(trace.get_length()):
            intersection_1 = trace_1_dict[timestep].intersection(input_aps)
            difference_1 = input_aps.difference(trace_1_dict[timestep])
            h_inter_1 = set()
            h_difference_1 = set()
            for l in intersection_1:
                h_inter_1.add(l+"#"+str(timestep))
            for l in difference_1:
                h_difference_1.add(l+"#"+str(timestep))
            trace_1_true_inputs[timestep] = h_inter_1
            trace_1_false_inputs[timestep] = h_difference_1
        
        true_input_0_list = []
        for timestep in range(trace.get_length()):
            true_input_0_list.append(trace_0_true_inputs[timestep])
        true_inputs_0 = set().union(*true_input_0_list)
        true_input_1_list = []
        for timestep in range(trace.get_length()):
            true_input_1_list.append(trace_1_true_inputs[timestep])
        true_inputs_1 = set().union(*true_input_1_list)
        false_input_0_list = []
        for timestep in range(trace.get_length()):
            append_not_set = set()
            for s in trace_0_false_inputs[timestep]:
                append_not_set.add("¬"+s)
            false_input_0_list.append(append_not_set)
        false_inputs_0 = set().union(*false_input_0_list)
        false_input_1_list = []
        for timestep in range(trace.get_length()):
            append_not_set = set()
            for s in trace_1_false_inputs[timestep]:
                append_not_set.add("¬"+s)
            false_input_1_list.append(append_not_set)
        false_inputs_1 = set().union(*false_input_1_list)

        ##Build sat formula from trace inputs as string (all true inputs and false inputs)
        wp_0_trace = "&".join(list(true_inputs_0.union(false_inputs_0)))
        wp_1_trace = "&".join(list(true_inputs_1.union(false_inputs_1)))

        ##Build sat formula from edge labels (negated)
        timestep = 0
        wp_0_help = edgelist_0[0].attr['label'].replace(" ","")
        wp_1_help = edgelist_1[0].attr['label'].replace(" ","")
        wp_0_list = re.split('∧|∨', wp_0_help)
        wp_1_list = re.split('∧|∨', wp_1_help)
        wp_0_0 = wp_0_list[0] + "#" + "0"
        wp_1_0 = wp_1_list[0] + "#" + "0"
        wp_0 = wp_0_0
        wp_1 = wp_1_0
        index = 1
        for el in wp_0_help[1:]:
            if el == '∧':
                wp_0 = wp_0 + " & " + wp_0_list[index] + "#" + str(timestep)
                index = index + 1
            else:
                if el == '∨':
                    wp_0 = wp_0 + " | " + wp_0_list[index] + "#" + str(timestep)
                    index = index + 1
        index = 1
        for el in wp_1_help[1:]:
            if el == '∧':
                wp_1 = wp_1 + " & " + wp_1_list[index] + "#" + str(timestep)
                index = index + 1
            else:
                if el == '∨':
                    wp_1 = wp_1 + " | " + wp_1_list[index] + "#" + str(timestep)
                    index = index + 1
        wp_0 = "(¬(" + wp_0 + "))"
        wp_1 = "(¬(" + wp_1 + "))"
        timestep = 1
        for edge_0, edge_1 in zip(edgelist_0[1:], edgelist_1[1:]):
            wp_0_help = wp_0_help = edge_0.attr['label'].replace(" ","")
            wp_1_help = wp_1_help = edge_1.attr['label'].replace(" ","")
            wp_0_list = re.split('∧|∨', wp_0_help)
            wp_1_list = re.split('∧|∨', wp_1_help)
            wp_0_1 = "(¬(" + wp_0_list[0] + "#" + str(timestep)
            wp_1_1 = "(¬(" + wp_1_list[0] + "#" + str(timestep)
            index = 1
            for el in wp_0_help[1:]:
                if el == '∧':
                    wp_0_1 = wp_0_1 + " & " + wp_0_list[index] + "#" + str(timestep)
                    index = index + 1
                else:
                    if el == '∨':
                        wp_0_1 = wp_0_1 + " | " + wp_0_list[index] + "#" + str(timestep)
                        index = index + 1
            index = 1
            for el in wp_1_help[1:]:
                if el == '∧':
                    wp_1_1 = wp_1_1 + " & " + wp_1_list[index] + "#" + str(timestep)
                    index = index + 1
                else:
                    if el == '∨':
                        wp_1_1 = wp_1_1 + " | " + wp_1_list[index] + "#" + str(timestep)
                        index = index + 1
            wp_0 = wp_0 + " & " + wp_0_1 + "))"
            wp_1 = wp_1 + " & " + wp_1_1 + "))"
            timestep = timestep + 1

        #construct cnf
        cnf_wp_0, aps_0 = CnfFromString.create(wp_0.replace("¬","-"))
        cnf_wp_1, aps_1 = CnfFromString.create(wp_1.replace("¬","-"))
        cnf_wp_0_trace, aps_0_trace = CnfFromString.create(wp_0_trace)
        cnf_wp_1_trace, aps_1_trace = CnfFromString.create(wp_1_trace)
        aps_0 = {**aps_0, **aps_0_trace}
        aps_1 = {**aps_0, **aps_1_trace}

        #replace negation symbol with - to convert to int
        cnf_wp_0 = str(cnf_wp_0)
        cnf_wp_1 = str(cnf_wp_1)
        cnf_wp_0 = cnf_wp_0.replace("¬","-")
        cnf_wp_1 = cnf_wp_1.replace("¬","-")
        cnf_wp_0_trace = (str(cnf_wp_0_trace).replace("¬","-"))
        cnf_wp_1_trace = (str(cnf_wp_1_trace).replace("¬","-"))
        
        #construct a unique mapping from ap to int
        ap_to_int_map_0 = {}
        index = 1
        for ap in aps_0:
            if ap not in ap_to_int_map_0.keys():
                ap_to_int_map_0[ap.replace("¬","")] = index
                index = index +1
        ap_to_int_map_1 = {}
        index = 1
        for ap in aps_1:
            if ap not in ap_to_int_map_1.keys():
                ap_to_int_map_1[ap.replace("¬","")] = index
                index = index +1

        #for ever ap in cnf, convert to int according to map
        for ap in aps_0:
            cnf_wp_0 = cnf_wp_0.replace(ap.replace("¬",""),str(ap_to_int_map_0[ap.replace("¬","")]))
        for ap in aps_1:
            cnf_wp_1 = cnf_wp_1.replace(ap.replace("¬",""),str(ap_to_int_map_1[ap.replace("¬","")]))

        # build sat solver
        solver_0 = Glucose4()
        solver_1 = Glucose4()
        
        #split clauses
        cnf_wp_0 = cnf_wp_0.replace(" ","")
        cnf_wp_1 = cnf_wp_1.replace(" ","")
        clause_list_0 = cnf_wp_0.split("&")
        clause_list_1 = cnf_wp_1.split("&")
        split_clause_list_0 = []
        split_clause_list_1 = []
        cnf_wp_0_trace = (str(cnf_wp_0_trace)).replace(" ", "").replace("(","").replace(")","")
        cnf_wp_0_trace_split = cnf_wp_0_trace.split("&")
        cnf_wp_1_trace = (str(cnf_wp_1_trace)).replace(" ", "").replace("(","").replace(")","")
        cnf_wp_1_trace_split = cnf_wp_1_trace.split("&")

        #split each clause in literals, and convert to int
        for c in clause_list_0:
            c = c.replace("(","").replace(")","")
            c = c.split('|')
            int_c = list(map(int,c))
            split_clause_list_0.append(int_c)
        for c in clause_list_1:
            c = c.replace("(","").replace(")","")
            c = c.split('|')
            int_c = list(map(int,c))
            split_clause_list_1.append(int_c)
        #add each clause to sat solver
        for c in split_clause_list_0:
            solver_0.add_clause(c)
        for c in split_clause_list_1:
            solver_1.add_clause(c)

        #get trace as cnf and int encoded
        cnf_trace_encoded_0 = []
        for c in cnf_wp_0_trace_split:
            if c.startswith("-"):
                cnf_trace_encoded_0.append(ap_to_int_map_0[c.replace("-","")]*-1)
            else:
                cnf_trace_encoded_0.append(ap_to_int_map_0[c.replace("-","")])
        cnf_trace_encoded_1 = []
        for c in cnf_wp_1_trace_split:
            if c.startswith("-"):
                cnf_trace_encoded_1.append(ap_to_int_map_1[c.replace("-","")]*-1)
            else:
                cnf_trace_encoded_1.append(ap_to_int_map_1[c.replace("-","")])

        #try to solve and get unsat core
        assumpt_0 = cnf_trace_encoded_0
        core_list_0 = []
        while (solver_0.solve(assumptions = assumpt_0) != True):
            core = solver_0.get_core()
            core_list_0.append(core)
            map(lambda x: x*-1,core)
            deleted = [item for item in assumpt_0 if item not in core]
            assumpt_0 = deleted
        assumpt_1 = cnf_trace_encoded_1
        core_list_1 = []
        while (solver_1.solve(assumptions = assumpt_1) != True):
            core = solver_1.get_core()
            core_list_1.append(core)
            map(lambda x: x*-1,core)
            deleted = [item for item in assumpt_1 if item not in core]
            assumpt_1 = deleted
        solver_0.delete()
        solver_1.delete()

        ## reconstruct aps X timestep:
        candidate_list_0 = []
        for cl in core_list_0:
            candidate = []
            for c in cl:
                ap = list(ap_to_int_map_0.keys())[list(ap_to_int_map_0.values()).index(abs(c))]
                ap_split_timestep = ap.split('#')
                if (c < 0):
                    candidate.append((ap_split_timestep[0],int(ap_split_timestep[1]),0,0))
                else:
                    candidate.append((ap_split_timestep[0],int(ap_split_timestep[1]),1,0))
            candidate_list_0.append(candidate)
        candidate_list_1 = []
        for cl in core_list_1:
            candidate = []
            for c in cl:
                ap = list(ap_to_int_map_1.keys())[list(ap_to_int_map_1.values()).index(abs(c))]
                ap_split_timestep = ap.split('#')
                if (c < 0):
                    candidate.append((ap_split_timestep[0],int(ap_split_timestep[1]),0,1))
                else:
                    candidate.append((ap_split_timestep[0],int(ap_split_timestep[1]),1,1))
            candidate_list_1.append(candidate)

        #compute new input set for each candidate where candidate elements are flipped
        cause_candidate_index_to_inputs_map_0 = {}
        index = 0
        new_canditate_list_0 = []
        for lst in candidate_list_0:
            for elm in lst:
                new_canditate_list_0.append(elm)
        new_canditate_list_1 = []
        
        for lst in candidate_list_1:
            for elm in lst:
                new_canditate_list_1.append(elm)
        candidate_list_0 = [new_canditate_list_0]
        candidate_list_1 = [new_canditate_list_1]
        
        for cc in candidate_list_0:
            tmp_true = true_inputs_0
            tmp_false = false_inputs_0
            for (ap,t,b,tr) in cc:
                #flip this ap in the set of inputs
                if (b == 0):
                    tmp_false.remove(("¬"+ap+"#"+str(t)))
                    tmp_true.add((ap+"#"+str(t)))
                else:
                    tmp_true.remove((ap+"#"+str(t)))
                    tmp_false.add(("¬"+ap+"#"+str(t)))
            cause_candidate_index_to_inputs_map_0[index] = tmp_true.union(tmp_false)
            index = index + 1
        cause_index_to_list_of_inputap_to_bool_0 = {}
        for cause_index in cause_candidate_index_to_inputs_map_0:
            list_of_inputap_to_bool_0 = []
            for timestep in range(trace.get_length()):
                ap_to_bool_dict = {}
                list_of_inputap_to_bool_0.append(ap_to_bool_dict)
            for ap in cause_candidate_index_to_inputs_map_0[cause_index]:
                split = ap.split("#")
                timestep = split[1]
                ap_raw = split[0]
                if ap_raw.startswith("¬"):
                    list_of_inputap_to_bool_0[int(timestep)][ap_raw.replace("¬","")] = 0
                else:
                    list_of_inputap_to_bool_0[int(timestep)][ap_raw] = 1
            cause_index_to_list_of_inputap_to_bool_0[cause_index] = list_of_inputap_to_bool_0
            
        cause_candidate_index_to_inputs_map_1 = {}
        index = 0
        for cc in candidate_list_1:
            tmp_true = true_inputs_1
            tmp_false = false_inputs_1
            for (ap,t,b,tr) in cc:
                #triple ap,timestep,Bool
                #flip this ap in the set of inputs
                if (b == 0):
                    tmp_false.remove(("¬"+ap+"#"+str(t)))
                    tmp_true.add((ap+"#"+str(t)))
                else:
                    tmp_true.remove((ap+"#"+str(t)))
                    tmp_false.add(("¬"+ap+"#"+str(t)))
            cause_candidate_index_to_inputs_map_1[index] = tmp_true.union(tmp_false)
            index = index + 1
        cause_index_to_list_of_inputap_to_bool_1 = {}
        for cause_index in cause_candidate_index_to_inputs_map_1:
            list_of_inputap_to_bool_1 = []
            for timestep in range(trace.get_length()):
                ap_to_bool_dict = {}
                list_of_inputap_to_bool_1.append(ap_to_bool_dict)
            for ap in cause_candidate_index_to_inputs_map_1[cause_index]:
                split = ap.split("#")
                timestep = split[1]
                ap_raw = split[0]
                if ap_raw.startswith("¬"):
                    list_of_inputap_to_bool_1[int(timestep)][ap_raw.replace("¬","")] = 0
                else:
                    list_of_inputap_to_bool_1[int(timestep)][ap_raw] = 1
            cause_index_to_list_of_inputap_to_bool_1[cause_index] = list_of_inputap_to_bool_1
        return tracemaps, cause_index_to_list_of_inputap_to_bool_0[0], cause_index_to_list_of_inputap_to_bool_1[0], candidate_list_0[0], candidate_list_1[0],

    # negate the cause and flip them accordingly in the trace
    def negate_cause(cause0, cause1, trace, all_aps):
        trace_0_dict = {}
        trace_1_dict = {}
        for k in range(trace.get_length()):
            trace0 = set()
            trace1 = set()
            current_values = trace.value_at(k)
            for ap in current_values:
                if ap.split("_")[len(ap.split("_"))-1] == "0":
                    trace0.add("_".join(ap.split("_")[:len(ap.split("_"))-1]))
                elif ap.split("_")[len(ap.split("_"))-1] == "1":
                    trace1.add("_".join(ap.split("_")[:len(ap.split("_"))-1]))
            trace_0_dict[k] = trace0
            trace_1_dict[k] = trace1
        input_aps = all_aps[0]
        trace_0_true_inputs = {}
        trace_0_false_inputs = {}
        trace_1_true_inputs = {}
        trace_1_false_inputs = {}
        for timestep in range(trace.get_length()):
            intersection_0 = trace_0_dict[timestep].intersection(input_aps)
            difference_0 = input_aps.difference(trace_0_dict[timestep])
            h_inter_0 = set()
            h_difference_0 = set()
            for l in intersection_0:
                h_inter_0.add(l+"#"+str(timestep))
            for l in difference_0:
                h_difference_0.add(l+"#"+str(timestep))
            trace_0_true_inputs[timestep] = h_inter_0
            trace_0_false_inputs[timestep] = h_difference_0
        
        for timestep in range(trace.get_length()):
            intersection_1 = trace_1_dict[timestep].intersection(input_aps)
            difference_1 = input_aps.difference(trace_1_dict[timestep])
            h_inter_1 = set()
            h_difference_1 = set()
            for l in intersection_1:
                h_inter_1.add(l+"#"+str(timestep))
            for l in difference_1:
                h_difference_1.add(l+"#"+str(timestep))
            trace_1_true_inputs[timestep] = h_inter_1
            trace_1_false_inputs[timestep] = h_difference_1

        true_input_0_list = []
        for timestep in range(trace.get_length()):
            true_input_0_list.append(trace_0_true_inputs[timestep])
        true_inputs_0 = set().union(*true_input_0_list)
        true_input_1_list = []
        for timestep in range(trace.get_length()):
            true_input_1_list.append(trace_1_true_inputs[timestep])
        true_inputs_1 = set().union(*true_input_1_list)
        false_input_0_list = []
        for timestep in range(trace.get_length()):
            append_not_set = set()
            for s in trace_0_false_inputs[timestep]:
                append_not_set.add("¬"+s)
            false_input_0_list.append(append_not_set)
        false_inputs_0 = set().union(*false_input_0_list)
        false_input_1_list = []
        for timestep in range(trace.get_length()):
            append_not_set = set()
            for s in trace_1_false_inputs[timestep]:
                append_not_set.add("¬"+s)
            false_input_1_list.append(append_not_set)
        false_inputs_1 = set().union(*false_input_1_list)

        ##compute new input set for each candidate where candidate elements are flipped
        cause_candidate_index_to_inputs_map_0 = {}
        index = 0
        cause0 = [cause0]
        cause1 = [cause1]
        for cc in cause0:
            tmp_true = true_inputs_0
            tmp_false = false_inputs_0
            for (ap,t,b,tr) in cc:
                #print(ap +","+str(t)+str(b)+str(tr))
                #triple ap,timestep,Bool
                #flip this ap in the set of inputs
                if (b == 0):
                    tmp_false.remove(("¬"+ap+"#"+str(t)))
                    tmp_true.add((ap+"#"+str(t)))
                else:
                    tmp_true.remove((ap+"#"+str(t)))
                    tmp_false.add(("¬"+ap+"#"+str(t)))
            cause_candidate_index_to_inputs_map_0[index] = tmp_true.union(tmp_false)
            index = index + 1
        cause_index_to_list_of_inputap_to_bool_0 = {}
        for cause_index in cause_candidate_index_to_inputs_map_0:
            list_of_inputap_to_bool_0 = []
            for timestep in range(trace.get_length()):
                ap_to_bool_dict = {}
                list_of_inputap_to_bool_0.append(ap_to_bool_dict)
            for ap in cause_candidate_index_to_inputs_map_0[cause_index]:
                split = ap.split("#")
                timestep = split[1]
                ap_raw = split[0]
                if ap_raw.startswith("¬"):
                    list_of_inputap_to_bool_0[int(timestep)][ap_raw.replace("¬","")] = 0
                else:
                    list_of_inputap_to_bool_0[int(timestep)][ap_raw] = 1
            cause_index_to_list_of_inputap_to_bool_0[cause_index] = list_of_inputap_to_bool_0
            
        cause_candidate_index_to_inputs_map_1 = {}
        index = 0
        for cc in cause1:
            tmp_true = true_inputs_1
            tmp_false = false_inputs_1
            for (ap,t,b,tr) in cc:
                #triple ap,timestep,Bool
                #flip this ap in the set of inputs
                if (b == 0):
                    tmp_false.remove(("¬"+ap+"#"+str(t)))
                    tmp_true.add((ap+"#"+str(t)))
                else:
                    tmp_true.remove((ap+"#"+str(t)))
                    tmp_false.add(("¬"+ap+"#"+str(t)))
            cause_candidate_index_to_inputs_map_1[index] = tmp_true.union(tmp_false)
            index = index + 1
        cause_index_to_list_of_inputap_to_bool_1 = {}
        for cause_index in cause_candidate_index_to_inputs_map_1:
            list_of_inputap_to_bool_1 = []
            for timestep in range(trace.get_length()):
                ap_to_bool_dict = {}
                list_of_inputap_to_bool_1.append(ap_to_bool_dict)
            for ap in cause_candidate_index_to_inputs_map_1[cause_index]:
                split = ap.split("#")
                timestep = split[1]
                ap_raw = split[0]
                if ap_raw.startswith("¬"):
                    list_of_inputap_to_bool_1[int(timestep)][ap_raw.replace("¬","")] = 0
                else:
                    list_of_inputap_to_bool_1[int(timestep)][ap_raw] = 1
            cause_index_to_list_of_inputap_to_bool_1[cause_index] = list_of_inputap_to_bool_1
        return None, cause_index_to_list_of_inputap_to_bool_0[0], cause_index_to_list_of_inputap_to_bool_1[0]


    # We assume the original formula to be in ENF! negations only in front of equiv, implication or ap
    def annotate_original_formula(self, orig_formula):
        init_node = self.aut.get_init_node()
        self.help_annotate(init_node, orig_formula)
    #Follows the original formula to insert a mapping from the NNF formula to the original formula as additional edges
    #in the automaton. For the equivalence case, two of the 4 subformulas are chosen.
    def help_annotate(self, node, orig_formula):
        formula = node.get_label()
        node.set_original_formula(orig_formula)
        edgelist = self.aut.get_outgoing_formula_edges(node)
        if not edgelist:
            return
        if not orig_formula:
            return
        if (orig_formula._is(op.Implies)) or (orig_formula._is(op.nImplies)):
            if formula._is(op.Or):
                self.help_annotate(edgelist[0].get_targets()[0], orig_formula[0])
                self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[0]])
                self.help_annotate(edgelist[1].get_targets()[0], orig_formula[1])
                self.aut.create_original_formula_edge(node, [edgelist[1].get_targets()[0]])
                return
            if formula._is(op.And):
                self.help_annotate(edgelist[0].get_targets()[0], orig_formula[0])
                self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[0]])
                self.help_annotate(edgelist[0].get_targets()[1], orig_formula[1])
                self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[1]])
                return
            print("Unreachable code")
            return
        if (orig_formula._is(op.Equiv)) or (orig_formula._is(op.nEquiv)):
            if formula._is(op.Or):
                l_edgelist = self.aut.get_outgoing_formula_edges(edgelist[0].get_targets()[0])  # depends on negation previously
                r_edgelist = self.aut.get_outgoing_formula_edges(edgelist[1].get_targets()[0])
                childll = l_edgelist[0].get_targets()[0]
                childlr = l_edgelist[0].get_targets()[1]
                childrl = r_edgelist[0].get_targets()[0]
                childrr = r_edgelist[0].get_targets()[1]# introduce significace of not here!
                self.aut.join_highlights_subtrees(childll, childrl)
                self.aut.join_highlights_subtrees(childlr, childrr)
                self.help_annotate(childll, orig_formula[0])
                self.help_annotate(childlr, orig_formula[1])
                self.aut.create_original_formula_edge(node, [childll])
                self.aut.create_original_formula_edge(node, [childlr])
                return
            if formula._is(op.And):
                l_edgelist = self.aut.get_outgoing_formula_edges(edgelist[0].get_targets()[0])  # depends on negation previously
                r_edgelist = self.aut.get_outgoing_formula_edges(edgelist[0].get_targets()[1])
                childll = l_edgelist[0].get_targets()[0]
                childlr = l_edgelist[1].get_targets()[0]
                childrl = r_edgelist[0].get_targets()[0]
                childrr = r_edgelist[1].get_targets()[0]  # introduce significace of not here!
                self.aut.join_highlights_subtrees(childll, childrl)
                self.aut.join_highlights_subtrees(childlr, childrr)
                self.help_annotate(childll, orig_formula[0])
                self.help_annotate(childlr, orig_formula[1])
                self.aut.create_original_formula_edge(node, [childll])
                self.aut.create_original_formula_edge(node, [childlr])
                return
            print("Unreachable code")
            return
        if formula._is(op.And):
            edge = edgelist[0].get_targets()
            i = 0
            for e in edge:
                self.help_annotate(e, orig_formula[i])
                self.aut.create_original_formula_edge(node, [e])
                i = i + 1
            return
        if formula._is(op.Or):
            i = 0
            for e in edgelist:
                self.help_annotate(e.get_targets()[0], orig_formula[i])
                self.aut.create_original_formula_edge(node, [e.get_targets()[0]])
                i = i + 1
            return
        if formula._is(op.ap) or formula._is(op.tt) or formula._is(op.ff):
            return
        if formula._is(op.Not):
            print("formula (not original) is Not")
            return
        if formula._is(op.X):
            self.help_annotate(edgelist[0].get_targets()[0], orig_formula[0])
            self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[0]])
            return
        if formula._is(op.U):
            self.help_annotate(edgelist[0].get_targets()[0], orig_formula[0])
            self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[0]])
            self.help_annotate(edgelist[1].get_targets()[0], orig_formula[1])
            self.aut.create_original_formula_edge(node, [edgelist[1].get_targets()[0]])
            return
        if formula._is(op.R):
            self.help_annotate(edgelist[0].get_targets()[0], orig_formula[0])
            self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[0]])
            self.help_annotate(edgelist[1].get_targets()[0], orig_formula[1])
            self.aut.create_original_formula_edge(node, [edgelist[1].get_targets()[0]])
            return
        if formula._is(op.G):
            self.help_annotate(edgelist[0].get_targets()[0], orig_formula[0])
            self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[0]])
            return
        if formula._is(op.F):
            self.help_annotate(edgelist[0].get_targets()[0], orig_formula[0])
            self.aut.create_original_formula_edge(node, [edgelist[0].get_targets()[0]])
            return
        else:
            print("This state should not be reached.")
            print(formula.to_str())
            sys.exit()