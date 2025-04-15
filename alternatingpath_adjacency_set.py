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
        self.neighbours: set[Node] = set()

    def __repr__(self) -> str:
        return f"<{self.clause.name},{self.literal},{self.direction}>"


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
                out_nodes.add(Node(literal, clause, "out"))
                in_nodes.add(Node(literal, clause, "in"))
        return out_nodes, in_nodes

    def construct_inclause_edges(self):
        for in_node in self.in_nodes:
            for out_node in self.out_nodes:
                if (
                    in_node.clause == out_node.clause
                    and in_node.literal != out_node.literal
                ):
                    self.create_edge(in_node, out_node)

    def construct_betweenclause_edges(self):
        for out_node in self.out_nodes:
            for in_node in self.in_nodes:
                different_signs = out_node.literal.negative != in_node.literal.negative
                mguExists = mgu(out_node.literal.atom, in_node.literal.atom) != None
                if mguExists and different_signs:
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
        print(neighbouring_nodes)
        return neighbouring_nodes

    def get_rel_neighbourhood(self, from_clauses: ClauseSet, distance: int):

        neighbourhood = self.clauses_to_nodes(from_clauses)
        for _ in range(2 * distance - 1):
            neighbourhood |= self.extend_neighbourhood(neighbourhood)

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
