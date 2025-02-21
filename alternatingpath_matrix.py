from clausesets import ClauseSet
from alternatingpath_abstract import RelevanceGraph
from fofspec import FOFSpec
from literals import Literal
from clauses import Clause

class Node:
    def __init__(self, literal: Literal, clause: Clause, direction) -> None:
        self.literal: Literal = literal
        self.clause: Clause = clause
        self.direction = direction

    def __repr__(self) -> str:
        return f"<{self.clause.name},{self.literal},{self.direction}>"

class MatrixRelevanceGraph(RelevanceGraph):

    def construct_graph(self, clause_set):
       pass


# Argument vorbereiten
problem = FOFSpec()
for file in ["PyRes/EXAMPLES/PUZ001-1.p"]:
    problem.parse(file)
cnf = problem.clausify()


nodes = []
for clause in cnf.clauses:
    for literal in clause.literals:
        for direction in ["in", "out"]:
            nodes.append(Node(literal, clause, direction))
node_to_int = {node: index for index, node in enumerate(nodes)}

# Matrix erstellen
matrix = [[float("inf")]*len(nodes)]*len(nodes)

# In-clause-edges setzen
for in_node in nodes:
    in_node_index = node_to_int[in_node]
    for out_node in nodes:
        out_node_index = node_to_int[out_node]
        if in_node == out_node:
            matrix[in_node_index][out_node_index] = 0
            matrix[out_node_index][in_node_index] = 0
        elif (
            in_node.clause == out_node.clause
            and in_node.literal != out_node.literal
        ):
            matrix[in_node_index][out_node_index] = 1
            matrix[out_node_index][in_node_index] = 1

print('\n'.join([''.join(['{:4}'.format(item) for item in row]) for row in matrix]))
# Between-clause-edges setzen

# Dijkstra durchführen
