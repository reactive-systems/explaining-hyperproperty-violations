#import spot
from formula import formula as spot
from operators import op
import pygraphviz as viz
import collections, numpy

class Node:
    label = None
    init = None
    accepting = None
    original = None
    result_array = None
    reason_array = None
    joint_array =  None
    outgoing_edges = None
    formula = None
    formula_edges = None
    orig_formula_edges = None
    original_formula = None
    id = None
    is_joint = None

    def set_outgoing_edges(self, edges):
        self.outgoing_edges = edges

    def __init__(self,  label, original, init, accepting, id = None):
        self.label = label
        self.init = init
        self.original = original
        self.accepting = accepting
        self.counter = id
        self.is_joint = False

    def __eq__(self, other):
        if self.id != other.id:
            return False
        return self.label.to_str() == other.label.to_str() and self.accepting == other.accepting

    def __hash__(self):
        return hash(self.label)
    def get_formula(self):
        return self.formula
    def get_label(self):
        return self.label
    def get_formula_edges(self):
        return self.formula_edges
    def get_original_formula_edges(self):
        return self.formula_edges
    def is_init(self):
        return self.init
    def is_accepting(self):
        return self.accepting
    def is_original(self):
        return self.original
    def init_result_array(self, x):
        self.result_array = [spot.ff() for i in range(x)]
        self.reason_array = [{} for i in range(x)]
    def init_joint_array(self, x):
        self.joint_array = [spot.ff() for i in range(x)]
    def set_array_at(self, x, value):
        self.result_array[x] = value
    def set_original_formula(self, formula):
        self.original_formula = formula
    def get_original_formula(self):
        return self.original_formula
    def get_id(self):
        return self.id
    def get_result_at(self,x):
        if x > len(self.result_array)-1:
            return spot.ff()
        return self.result_array[x]
    def get_reason_at(self,x):
        return self.reason_array[x]
    def set_result_at(self,x, y):
        self.result_array[x] = y
    def set_reason_at(self, x, y):
        self.reason_array[x] = y
    def get_outgoing_edges(self):
        return self.outgoing_edges
    def join_highlight(self, node):
        self.is_joint = True
        result = []
        for x in range(len(self.result_array)):
            if self.result_array[x] is 1 or node.result_array[x] is 1:
                result.append(1)
            else:
                result.append(0)
        self.joint_array = result

class Edge:
    source = None
    targets = None
    universal = None


    def __init__(self, source, targets):
        self.source = source
        self.targets = targets
        self.universal = True if len(targets) > 1 else False

    #TODO: check this
    def __eq__(self, other):
        if self.source.id != other.source.id:
            return False
        if self.source.get_label() == other.source.get_label():
            if (len(self.get_targets())) != len(other.get_targets()):
                return False
            i = 0
            for target in self.get_targets():
                for t2 in other.get_targets():
                    if target.get_label() == t2.get_label:
                        i = i + 1
                if i == len(self.get_targets()) and i == len(other.get_targets()):
                    return True
        return False
    #TODO: refine
    def __hash__(self):
        return hash(self.source)

    def get_source(self):
        return self.source

    def get_targets(self):
        return self.targets

    def is_universal(self):
        return self.universal


class Automaton:
    nodes = None
    edges = None
    formula_edges = None
    original_formula_edges = None
    nodes_original = None
    nodes_highlight = None
    counter = None

    def __init__(self):
        self.nodes = []
        self.edges = []
        self.formula_edges = []
        self.original_formula_edges = []
        self.nodes_original = set()
        self.nodes_highlight = set()
        self.counter = 0

    def create_node(self, label, original, init, accepting):
        node = Node(label, init, original, init, accepting, self.counter)
        self.counter = self.counter + 1
        self.add_node(node)

    def add_node(self, node):
        if not node.id:
            node.id = self.counter
            self.counter = self.counter + 1
        if (node.is_original):
            self.nodes_original.add(node)
        else:
            self.nodes_highlight.add(node)
        self.nodes.append(node)

    def create_edge(self, source, target):
        test = False
        e = Edge(source,target)
        for edge in self.edges:
            if edge == e:
                test = True
        if not test:
            self.edges.append(Edge(source,target))

    def create_formula_edge(self, source, target):
        test = False
        e = Edge(source, target)
        for edge in self.formula_edges:
            if edge == e:
                test = True
        if not test:
            self.formula_edges.append(e)

    def create_original_formula_edge(self, source, target):
        test = False
        e = Edge(source, target)
        for edge in self.original_formula_edges:
            if edge == e:
                test = True
        if not test:
            self.original_formula_edges.append(e)

    def get_nodes(self):
        return self.nodes

    def get_edges(self):
        return self.edges

    def get_outgoing_edges(self, node):
        edgeset = []
        for e in self.edges:
            if e.source == node:
                edgeset.append(e)
        return edgeset
    def get_outgoing_formula_edges(self, node):
        edgeset = []
        for e in self.formula_edges:
            if e.source == node:
                edgeset.append(e)
        return edgeset

    def get_outgoing_original_formula_edges(self, node):
        edgeset = []
        for e in self.original_formula_edges:
            if e.source == node:
                edgeset.append(e)
        return edgeset

    def get_node(self, string):
        for node in self.nodes:
            if node.label == string:
                return node

    def get_ingoing_edges(self, node):
        edgeset = set()
        for e in self.edges:
            if e.target == node:
                edgeset.add(e)
        return edgeset

    def get_init_node(self):
        for node in self.nodes:
            if node.is_init():
                return node

    def join_highlights_subtrees(self, nodel, noder):
        nodel.join_highlight(noder)
        edgelistl = self.get_outgoing_formula_edges(nodel)
        edgelistr = self.get_outgoing_original_formula_edges(noder)
        for x in range(len(edgelistl)):
            for y in range(len(edgelistl[x].get_targets())):
                childl = edgelistl[x].get_targets()[y]
                childr = edgelistr[x].get_targets()[y]
                childl.join_highlights(childr)

#deprecated
    def to_dot(self):
        counter = 10 #cannot be one or zero bc true false
        out_graph = viz.AGraph(directed=True, strict=False)
        for edge in self.get_edges():
            out_graph.add_node(edge.get_source().get_label(), label=edge.get_source().get_label())
            for target in edge.get_targets():
                out_graph.add_node(target.get_label(), label = target.get_label())
            out_graph.add_node(counter, shape="point", width=0)

            out_graph.add_edge(edge.get_source().get_label(), counter, dir="none")
            for target in edge.get_targets():
                out_graph.add_edge(counter, target.get_label())
            counter += 1
        return out_graph

    def preprocess(self, length):
        for node in self.nodes:
            node.set_outgoing_edges(self.get_outgoing_edges(node))
            node.init_result_array(length)
            node.init_joint_array(length)

    def count_events(self):
        counter = 0
        for node in self.nodes:
            if node.label.operator is op.ap:
                n = numpy.array(node.joint_array)
                di = collections.Counter(n)
                counter = counter + di[1]
        return counter

