from clauses import Clause
from clausesets import ClauseSet
from literals import Literal
from unification import mgu
from collections import defaultdict
from alternatingpath_abstract import RelevanceGraph


class Node:
    def __init__(self, literal: Literal, clause: Clause) -> None:
        self.literal: Literal = literal
        self.clause: Clause = clause
        self.neighbours: set[Node] = set()

    def __repr__(self) -> str:
        return f"<{self.clause.name},{self.literal}>"


class AdjacencySetRelevanceGraph(RelevanceGraph):

    def construct_graph(self, clause_set: ClauseSet) -> None:
        self.out_nodes, self.in_nodes = self.construct_nodes(clause_set)
        self.construct_inclause_edges()
        self.construct_betweenclause_edges()

    def create_edge(self, node1, node2):
        node1.neighbours.add(node2)
        node2.neighbours.add(node1)

    @staticmethod
    def construct_nodes(clause_set: ClauseSet):
        out_nodes = set()
        in_nodes = set()
        for clause in clause_set.clauses:
            for literal in clause.literals:
                out_nodes.add(Node(literal, clause))
                in_nodes.add(Node(literal, clause))
        return out_nodes, in_nodes

    def construct_inclause_edges(self):
        for in_node in self.in_nodes:
            for out_node in self.out_nodes:
                if in_node.clause != out_node.clause:
                    continue
                if in_node.literal == out_node.literal:
                    continue
                self.create_edge(in_node, out_node)

    def construct_betweenclause_edges(self):
        for out_node in self.out_nodes:
            for in_node in self.in_nodes:
                if out_node.literal.negative == in_node.literal.negative:
                    continue
                if mgu(out_node.literal.atom, in_node.literal.atom) == None:
                    continue
                self.create_edge(in_node, out_node)

    def get_all_nodes(self):
        return self.out_nodes | self.in_nodes

    @staticmethod
    def nodes_to_clauses(nodes):
        return ClauseSet({node.clause for node in nodes})

    def clauses_to_nodes(self, clauses: ClauseSet):
        allNodes = self.get_all_nodes()
        nodesOfClauseSubset = {
            node for node in allNodes if node.clause in clauses.clauses
        }
        return nodesOfClauseSubset

    def extend_neighbourhood(self, subset: set[Node]):
        neighbouring_nodes = {
            neighbour for node in subset for neighbour in node.neighbours
        }
        return neighbouring_nodes

    def get_rel_neighbourhood(self, from_clauses: ClauseSet, distance: int):

        neighbourhood = self.clauses_to_nodes(from_clauses)
        for _ in range(2 * distance - 1):
            neighbourhood |= self.extend_neighbourhood(neighbourhood)

        clauses = self.nodes_to_clauses(neighbourhood)
        return clauses
