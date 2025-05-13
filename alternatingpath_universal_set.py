from clauses import Clause
from clausesets import ClauseSet
from literals import Literal
from unification import mgu
from collections import defaultdict
from alternatingpath_abstract import RelevanceGraph


class Node:
    def __init__(self, literal: Literal, clause: Clause, direction) -> None:
        self.literal: Literal = literal
        self.clause: Clause = clause
        self.direction = direction

    def __repr__(self) -> str:
        return f"<{self.clause.name},{self.literal},{self.direction}>"


class Edge:
    def __init__(self, node1: Node, node2: Node) -> None:
        self.node1: Node = node1
        self.node2: Node = node2

    def __repr__(self) -> str:
        return f"Edge: {self.node1} - {self.node2}"


class UniversalSetRelevanceGraph(RelevanceGraph):

    def construct_graph(self, clause_set: ClauseSet) -> None:
        self.out_nodes, self.in_nodes = self.construct_nodes(clause_set)
        self.edges: set[Edge] = (
            self.construct_inclause_edges() | self.construct_betweenclause_edges()
        )

    @staticmethod
    def construct_nodes(clause_set: ClauseSet):
        out_nodes = set()
        in_nodes = set()
        for clause in clause_set.clauses:
            for literal in clause.literals:
                out_nodes.add(Node(literal, clause, "out"))
                in_nodes.add(Node(literal, clause, "in"))
        return out_nodes, in_nodes

    def construct_inclause_edges(self):
        in_clause_edges = set()
        for in_node in self.in_nodes:
            for out_node in self.out_nodes:
                if in_node.clause != out_node.clause:
                    continue
                if in_node.literal == out_node.literal:
                    continue
                in_clause_edges.add(Edge(in_node, out_node))
        return in_clause_edges

    def construct_betweenclause_edges(self):
        between_clause_edges = set()
        for out_node in self.out_nodes:
            for in_node in self.in_nodes:
                if out_node.literal.negative == in_node.literal.negative:
                    continue
                if mgu(out_node.literal.atom, in_node.literal.atom) == None:
                    continue
                between_clause_edges.add(Edge(out_node, in_node))
        return between_clause_edges

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

    @staticmethod
    def edge_neighb_of_subset(edge: Edge, subset: set[Node]):
        return (edge.node1 in subset) != (edge.node2 in subset)

    def get_neighbours(self, subset: set[Node]):
        neighbouring_edges = {
            edge for edge in self.edges
            if self.edge_neighb_of_subset(edge, subset)
        }
        self.edges -= neighbouring_edges
        neighbouring_nodes = {
            edge.node2 if edge.node1 in subset else edge.node1
            for edge in neighbouring_edges
        }
        return neighbouring_nodes

    def get_rel_neighbourhood(self, from_clauses: ClauseSet, distance: int):

        neighbourhood = self.clauses_to_nodes(from_clauses)
        for _ in range(2 * distance - 1):
            new_neighbours = self.get_neighbours(neighbourhood)
            neighbourhood |= new_neighbours

        clauses = self.nodes_to_clauses(neighbourhood)
        return clauses

    def to_mermaid(self, path: str) -> str:
        output: str = "flowchart TD"

        node_groups = defaultdict(list)

        nodes_list = list(self.get_all_nodes())
        nodes_sorted = sorted(
            nodes_list,
            key=lambda node: (
                -len(node.clause.literals),
                node.clause.name.casefold(),
                node.literal.__repr__().casefold(),
                node.direction.casefold(),
            ),
        )
        for node in nodes_sorted:
            node_groups[node.clause].append(node)
        node_groups: list = list(node_groups.values())
        for node_group in node_groups:
            node_group = list(node_group)
            group_output = f"\n\tsubgraph {node_group[0].clause.name}"
            for node in node_group:
                group_output += (
                    f'\n\t\t{node.__repr__()}["{node.literal},{node.direction}"]'
                )
            group_output += "\n\tend"
            output += group_output

        # Edges for keeping same literals in clause together
        output += "\n\t%% invisible edges (for better visualization)"
        for index, _ in enumerate(self.in_nodes):
            output += f"\n\t{2*index} ~~~ {2*index+1}"

        edges_sorted = sorted(
            list(self.edges),
            key=lambda edge: (
                edge.node1.clause != edge.node2.clause,
                nodes_sorted.index(edge.node1),
                nodes_sorted.index(edge.node2),
                edge.node1.clause.name.casefold(),
                edge.node1.literal.__repr__().casefold(),
                edge.node1.direction.casefold(),
            ),
        )
        current_edge_type: str = "in-clause"
        output += "\n\t%% in-clause edges"
        direction_fits: bool = True
        for edge in edges_sorted:
            if current_edge_type == "in-clause":
                if edge.node1.clause != edge.node2.clause:
                    current_edge_type = "between-clause"
                    output += "\n\t%% between-clause edges"
                if direction_fits:
                    output += f"\n\t{edge.node1.__repr__()} --- {edge.node2.__repr__()}"
                else:
                    output += f"\n\t{edge.node2.__repr__()} --- {edge.node1.__repr__()}"
                direction_fits = not direction_fits
            if current_edge_type == "between-clause":
                output += f"\n\t{edge.node1.__repr__()} --- {edge.node2.__repr__()}"

        node_strings = [f"{node}" for node in nodes_sorted]

        for index, string in enumerate(node_strings):
            output = output.replace(string, str(index))

        with open(path, "w") as f:
            f.write(output)
