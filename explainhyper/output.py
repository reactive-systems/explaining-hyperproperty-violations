#import spot
from operators import op
from formula import formula as spot
import json
import highlighter
import altautomaton
import re


def dump_json(automaton, filename = None):
    nodes = automaton.get_nodes()
    for n in nodes:
        dict = {}
        dict["id"] = n.get_label()
        dict["evaluation"] = n.result_array

        json_object = json.dumps(dict, indent=4)
        if filename:
            with open(f"{filename}.json", "a") as outfile:
                outfile.write(json_object)
        else:
            with open("table.json", "a") as outfile:
                outfile.write(json_object)


def table_to_cex(high, filename):
    with open(filename, "a") as file:
        file.write("HIGH:\n")
        nodes = high.aut.get_nodes()
        length = len(nodes[0].result_array)
        for i in range(length):
            for n in nodes:
                formula = spot.formula(n.get_label())
                if not formula._is(op.ap) and not formula._is(op.tt) and not formula._is(op.ff):
                    file.write(f"{n.get_label()}@{i}={n.get_result_at(i)}\n")


def automaton_to_json_formula(high, outName, negate):
    init_node = high.aut.get_init_node()
    dict = help_atofjson(init_node, high.aut)
    dict_new = {'name': 'root'}
    if negate:
        dict_new['hyperhyper'] = "EE"
    else:
        dict_new['hyperhyper'] = "AA"
    dict_new['children'] = dict
    with open(outName + ".json", "w") as outfile:
        outfile.write(json.dumps(dict_new, indent=4))
def indexmap_to_json(list, outfile):
    dict = {}
    dict["identifier"] = "state"
    dict["traces"] = list
    json_object = json.dumps(dict, indent=4)
    if outfile:
        with open(f"{outfile}.json", "w") as outfile:
            outfile.write(json_object)

def trace_to_json(all_aps, trace, outName, lassostart, list):
    dict_all = {}
    dict_var = {}
    dict_all["stateVariable"] = "state"
    aps_set = set()
    aps_set1 = set()
    aps_set2 = set()
    for n in all_aps[0]:
        aps_set.add(n)
        aps_set1.add(n+"_0")
        aps_set2.add(n + "_1")
        dict_type = {}
        dict_type["type"] = "input"
        dict_var[n] = dict_type
    for n in all_aps[1]:
        aps_set.add(n)
        aps_set1.add(n + "_0")
        aps_set2.add(n + "_1")
        dict_type = {}
        dict_type["type"] = "output"
        dict_var[n] = dict_type
    for n in all_aps[2]:
        aps_set.add(n)
        aps_set1.add(n + "_0")
        aps_set2.add(n + "_1")
        dict_type = {}
        dict_type["type"] = "latch"
        dict_var[n] = dict_type
    dict_all["variables"] = dict_var
    dict_all["lassoStart"] = lassostart
    list_of_list_of_dicts = []

    for i in range(trace.get_length()):
        list_of_dicts = []
        for n in range(2): #hard coded to forallforall and existsexists
            dicttimestep = {}
            if len(list) != 0:
                dicttimestep["state"] = list[n][i]
            else:
                dicttimestep["state"] = -1
            for x in aps_set:
                if (x + "_" + str(n) in trace.value_at(i)):
                    dicttimestep[x] = True
                else:
                    dicttimestep[x] = False
            list_of_dicts.append(dicttimestep)
        list_of_list_of_dicts.append(list_of_dicts)
    dict_all["timesteps"] = list_of_list_of_dicts
    return dict_all

def help_atofjson_original(node, aut):
    if not node.get_original_formula():
        return
    formula = node.get_original_formula()
    result = {}
    if node.is_joint:
        result["high"] = node.joint_array
    else:
        result["high"] = node.result_array
    result["isAtomic"] = False
    result["id"] = node.get_id()
    if formula._is(op.ap):
        array = re.sub(r'"([^:@=]+?)"', r'\1', formula.to_str()).rsplit("_",1)
        result['name'] = array[0]
        result['value'] = 200
        result["isAtomic"] = True
        result['variable'] = array[0]
        result['trace'] = int(array[1])
    if formula._is(op.tt):
        result['name'] = re.sub(r'"([^:@=]+?)"', r'\1', spot.formula.ff().to_str())
        return result
    if formula._is(op.ff):
        result['name'] = re.sub(r'"([^:@=]+?)"', r'\1', spot.formula.tt().to_str())
        return result
    if formula._is(op.Not):
        result['name'] = '!'
        childs = []
        dict = {}
        dict['id'] = aut.counter
        aut.counter = aut.counter + 1
        array = re.sub(r'"([^:@=]+?)"', r'\1', formula[0].to_str()).rsplit("_", 1)
        dict['name'] = array[0]
        dict['value'] = 200
        dict["isAtomic"] = True
        dict['variable'] = array[0]
        dict['trace'] = int(array[1])
        dict['high'] = node.result_array
        childs.append(dict)
        result['children'] = childs
        return result
    if formula._is(op.X):
        result['name'] = 'X'
    if formula._is(op.And):
        result['name'] = '&'
    if formula._is(op.Or):
        result['name'] = '|'
    if formula._is(op.U):
        result['name'] = 'U'
    #if formula._is(op.W):
    #    result['name'] = 'W'
    if formula._is(op.R):
        result['name'] = 'R'
    if formula._is(op.G):
        result['name'] = 'G'
    if formula._is(op.F):
        result['name'] = 'F'
    if formula._is(op.Implies):
        result['name'] = '->'
    if formula._is(op.Equiv):
        result['name'] = '<->'
    if formula._is(op.nImplies):
        result['name'] = '!->'
    if formula._is(op.nEquiv):
        result['name'] = '<!->'
    # TODO: check for else case
    child_list = []
    for edge in aut.get_outgoing_original_formula_edges(node):
        for child in edge.get_targets():
            #print("child: " + child.get_label().to_str())
            child_list.append(help_atofjson_original(child, aut))
    if child_list:
        result['children'] = child_list
    return result

#all operators are negated as in translator.negate
def help_atofjson(node, aut):
    #formula = spot.formula(node.get_label())
    if not node.get_original_formula():
        return
    formula = node.get_original_formula()
    result = {}
    result["high"] = node.result_array
    result["isAtomic"] = False
    result["id"] = node.get_id()
    if formula._is(op.ap):
        result['name'] = '!'
        childs = []
        dict = {}
        dict['id'] = aut.counter
        aut.counter = aut.counter + 1
        dict['name'] = re.sub(r'"([^:@=]+?)"', r'\1', formula.to_str())
        dict['value'] = 200
        dict['high'] = node.result_array
        dict['isAtomic'] = True

        childs.append(dict)
        result['children'] = childs
        return result
    if formula._is(op.tt):
        result['name'] = re.sub(r'"([^:@=]+?)"', r'\1', spot.formula.ff().to_str())
        return result
    if formula._is(op.ff):
        result['name'] = re.sub(r'"([^:@=]+?)"', r'\1', spot.formula.tt().to_str())
        return result
    if formula._is(op.Not):
        result['name'] = re.sub(r'"([^:@=]+?)"', r'\1', formula[0].to_str())
        result['value'] = 200
        result["isAtomic"] = True
        return result
    if formula._is(op.X):
        result['name'] = 'X'
    if formula._is(op.And):
        result['name'] = '|'
    if formula._is(op.Or):
        result['name'] = '&'
    if formula._is(op.U):
        result['name'] = 'R'
    #if formula._is(op.W):
    #    result['name'] = 'W'
    if formula._is(op.R):
        result['name'] = 'U'
    if formula._is(op.G):
        result['name'] = 'F'
    if formula._is(op.F):
        result['name'] = 'G'
    if formula._is(op.Implies):
        result['name'] = '->'
    if formula._is(op.Equiv):
        result['name'] = '<->'
    #TODO: check for else case
    child_list = []
    for edge in aut.get_outgoing_formula_edges(node):
        for child in edge.get_targets():
            child_list.append(help_atofjson(child, aut))
    if child_list:
        result['children'] = child_list
    return result

def formula_to_json(formula, outName):
    dict = help_ftojson(formula)
    dict_new = {'name': 'root'}
    dict_new['children']= dict
    with open(outName + ".json", "w") as outfile:
        outfile.write(json.dumps(dict_new, indent=4))



def help_ftojson(formula):
    result = {}
    if formula._is(op.ap):
        result['name'] = re.sub(r'"([^:@=]+?)"', r'\1', formula.to_str())
        result['value'] = 200
        return result
    if formula._is(op.tt) or formula._is(op.ff):
        result['name'] = re.sub(r'"([^:@=]+?)"', r'\1', formula.to_str())
        return result
    if formula._is(op.Not):
        result['name'] = '!'
    if formula._is(op.X):
        result['name'] = 'X'
    if formula._is(op.And):
        result['name'] = '&'
    if formula._is(op.Or):
        result['name'] = '|'
    if formula._is(op.U):
        result['name'] = 'U'
    if formula._is(op.W):
        result['name'] = 'W'
    if formula._is(op.R):
        result['name'] = 'R'
    if formula._is(op.G):
        result['name'] = 'G'
    if formula._is(op.F):
        result['name'] = 'F'
    child_list = []
    for child in formula:
        child_list.append(help_ftojson(child))
    if child_list:
        result['children'] = child_list
    return result

def automaton_to_json_formula(high, outName, negate):
    init_node = high.aut.get_init_node()
    dict = help_atofjson(init_node, high.aut)
    dict_new = {'name': 'root'}
    if negate:
        dict_new['hyperhyper'] = "AA"
    else:
        dict_new['hyperhyper'] = "EE"
    dict_new['children'] = dict
    with open(outName + ".json", "w") as outfile:
        outfile.write(json.dumps(dict_new, indent=4))

#all operators are negated as in translator.negate
def help_atofjson(node, aut):
    formula = node.get_label()
    result = {}
    result["high"] = node.result_array
    result["isAtomic"] = False
    result["id"] = node.get_id()
    if formula._is(op.ap):
        result['name'] = '!'
        childs = []
        dict = {}
        dict['id'] = aut.counter
        aut.counter = aut.counter + 1
        dict['name'] = re.sub(r'"([^:@=]+?)"', r'\1', formula.to_str())
        dict['value'] = 200
        dict['high'] = node.result_array
        dict['isAtomic'] = True

        childs.append(dict)
        result['children'] = childs
        return result
    if formula._is(op.tt):
        result['name'] = re.sub(r'"([^:@=]+?)"', r'\1', spot.formula.ff().to_str())
        return result
    if formula._is(op.ff):
        result['name'] = re.sub(r'"([^:@=]+?)"', r'\1', spot.formula.tt().to_str())
        return result
    if formula._is(op.Not):
        result['name'] = re.sub(r'"([^:@=]+?)"', r'\1', formula[0].to_str())
        result['value'] = 200
        result["isAtomic"] = True
        return result
    if formula._is(op.X):
        result['name'] = 'X'
    if formula._is(op.And):
        result['name'] = '|'
    if formula._is(op.Or):
        result['name'] = '&'
    if formula._is(op.U):
        result['name'] = 'R'
    #if formula._is(op.W):
    #    result['name'] = 'W'
    if formula._is(op.R):
        result['name'] = 'U'
    if formula._is(op.G):
        result['name'] = 'F'
    if formula._is(op.F):
        result['name'] = 'G'
    if formula._is(op.Implies):
        result['name'] = '->'
    if formula._is(op.Equiv):
        result['name'] = '<->'
    #TODO: check for else case
    child_list = []
    for edge in aut.get_outgoing_formula_edges(node):
        for child in edge.get_targets():
            child_list.append(help_atofjson(child, aut))
    if child_list:
        result['children'] = child_list
    return result

def formula_to_json(formula, outName):
    dict = help_ftojson(formula)
    dict_new = {'name': 'root'}
    dict_new['children']= dict
    with open(outName + ".json", "w") as outfile:
        outfile.write(json.dumps(dict_new, indent=4))



def help_ftojson(formula):
    result = {}
    if formula._is(op.ap):
        result['name'] = re.sub(r'"([^:@=]+?)"', r'\1', formula.to_str())
        result['value'] = 200
        return result
    if formula._is(op.tt) or formula._is(op.ff):
        result['name'] = re.sub(r'"([^:@=]+?)"', r'\1', formula.to_str())
        return result
    if formula._is(op.Not):
        result['name'] = '!'
    if formula._is(op.X):
        result['name'] = 'X'
    if formula._is(op.And):
        result['name'] = '&'
    if formula._is(op.Or):
        result['name'] = '|'
    if formula._is(op.U):
        result['name'] = 'U'
    if formula._is(op.W):
        result['name'] = 'W'
    if formula._is(op.R):
        result['name'] = 'R'
    if formula._is(op.G):
        result['name'] = 'G'
    if formula._is(op.F):
        result['name'] = 'F'
    child_list = []
    for child in formula:
        child_list.append(help_ftojson(child))
    if child_list:
        result['children'] = child_list
    return result


def to_json(high, outName, negate, dict_all):
    dict_new = dict_all
    init_node = high.aut.get_init_node()
    dict_new['plain'] = high.aut.get_init_node().get_original_formula().to_str()
    dict_formula = {}
    dict_formula['name'] = "root"
    dict_formula['id'] = -1
    dict = help_atofjson_original(init_node, high.aut)
    dict_formula['children'] = dict
    dict_new['tree'] = dict_formula
    if negate:
        dict_new['prefix'] = ["Forall", "Forall"]
    else:
        dict_new['prefix'] = ["Exists", "Exists"]
    with open(outName + ".json", "w") as outfile:
        outfile.write(json.dumps(dict_new, indent=4))




