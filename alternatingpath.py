from clauses import Clause
from clausesets import ClauseSet
from literals import Literal
from unification import mgu
from collections import defaultdict


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


class RelevanceGraph:
    def __init__(self, clause_set: ClauseSet) -> None:
        self.out_nodes, self.in_nodes = self.construct_nodes(clause_set)
        self.edges: set[Edge] = (
            self.construct_inclause_edges()
            | self.construct_betweenclause_edges()
        )

    @staticmethod
    def construct_nodes(clause_set: ClauseSet) -> tuple[set[Node]]:
        out_nodes = set[Node]()
        in_nodes = set[Node]()
        for clause in clause_set.clauses:
            for literal in clause.literals:
                out_nodes.add(Node(literal, clause, "out"))
                in_nodes.add(Node(literal, clause, "in"))
        return out_nodes, in_nodes

    def construct_inclause_edges(self) -> set[Edge]:
        in_clause_edges = set[Edge]()
        for in_node in self.in_nodes:
            for out_node in self.out_nodes:
                if (
                    in_node.clause == out_node.clause
                    and in_node.literal != out_node.literal
                ):
                    in_clause_edges.add(
                        Edge(in_node, out_node))
        return in_clause_edges

    def construct_betweenclause_edges(self) -> set[Edge]:
        between_clause_edges = set[Edge]()
        for out_node in self.out_nodes:
            for in_node in self.in_nodes:
                different_signs = (
                    out_node.literal.negative
                    != in_node.literal.negative
                )
                mguExists = mgu(
                    out_node.literal.atom,
                    in_node.literal.atom) != None
                if mguExists and different_signs:
                    between_clause_edges.add(
                        Edge(out_node, in_node))
        return between_clause_edges

    def get_all_nodes(self) -> set[Node]:
        return self.out_nodes | self.in_nodes

    @staticmethod
    def nodes_to_clauses(nodes: set[Node]) -> ClauseSet:
        clauses = ClauseSet()
        for node in nodes:
            clauses.addClause(node.clause)
        clauses.clauses = list(set(clauses.clauses))
        return clauses

    def clauses_to_nodes(self, clauses: ClauseSet) -> set[Node]:
        allNodes = self.get_all_nodes()
        nodesOfClauseSubset = filter(
            lambda node: node.clause in clauses.clauses, allNodes
        )
        return nodesOfClauseSubset

    @staticmethod
    def edge_neighb_of_subset(edge: Edge, subset: list[Node]) -> bool:
        return (edge.node1 in subset) != (edge.node2 in subset)

    def get_neighbours(self, subset: list[Node]) -> list[Node]:
        neighbouring_nodes: list[Node] = []
        neighbouring_edges: list[Edge] = filter(
            lambda edge: self.edge_neighb_of_subset(edge, subset),
            self.edges
        )

        for edge in neighbouring_edges:
            if edge.node1.clause in subset:
                neighbouring_nodes.append(object=edge.node2)
            else:
                neighbouring_nodes.append(edge.node1)
        return neighbouring_nodes

    def get_rel_neighbourhood(self, from_clauses: ClauseSet, distance: int) -> ClauseSet:

        neighbourhood: list[Node] = list(
            self.clauses_to_nodes(from_clauses))
        for _ in range(2 * distance - 1):
            new_neighbours = self.get_neighbours(neighbourhood)
            neighbourhood += new_neighbours

        clauses = self.nodes_to_clauses(neighbourhood)
        return clauses

    # def to_graphviz(self):
    #     import graphviz

    def to_mermaid(self) -> str:
        output: str = "flowchart TD"

        node_groups = defaultdict(list)

        nodes_list: list[Node] = list(self.get_all_nodes())
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

        # edgesSorted = sorted(list(self.edges), key=lambda edge: (edge.node1.clause.name.casefold(), edge.node1.literal.__repr__().casefold(), edge.node1.direction.casefold()))
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

        node_strings = list(map(lambda node: node.__repr__(), nodes_sorted))

        for index, string in enumerate(node_strings):
            output = output.replace(string, str(index))
        return output
