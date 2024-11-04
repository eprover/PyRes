from clauses import Clause
from clausesets import ClauseSet
from literals import Literal
from unification import mgu
from collections import defaultdict


class Node():
    def __init__(self, literal: Literal, clause: Clause, direction) -> None:
        self.literal: Literal = literal
        self.clause: Clause = clause
        self.direction = direction
    def getIdentifier(self) -> str:
        output: str = f"{self.literal}{self.clause.name}{self.direction}"
        replacementDict = {
            ",": "Comma",
            "~": "Not",
            "(": "Open",
            ")": "Close",
            "_": "Underscore",
            "|": "Or",
            ".": "Dot",
        }
        for old, new in replacementDict.items():
            output = output.replace(old, new)
        return output

class Edge():
    def __init__(self, node1: Node, node2: Node) -> None:
        self.node1: Node = node1
        self.node2: Node = node2

class RelevanceGraph():
    def __init__(self, clauseSet: ClauseSet) -> None:
        self.outNodes, self.inNodes = self.constructNodes(clauseSet)
        self.edges = self.constructInClauseEdges().union(self.constructBetweenClauseEdges())

    def constructNodes(self, clauseSet: ClauseSet) -> tuple[set[Node]]:
        outNodes = set[Node]()
        inNodes = set[Node]()
        for clause in clauseSet.clauses:
            for literal in clause.literals:
                outNodes.add(Node(literal, clause, "out"))
                inNodes.add(Node(literal, clause, "in"))
        return outNodes, inNodes

    def constructInClauseEdges(self) -> set[Edge]:
        inClauseEdges = set[Edge]()
        for inNode in self.inNodes:
            for outNode in self.outNodes:
                if (inNode.clause == outNode.clause and inNode.literal != outNode.literal):
                    inClauseEdges.add(Edge(inNode, outNode))
        return inClauseEdges

    def constructBetweenClauseEdges(self) -> set[Edge]:
        betweenClauseEdges = set[Edge]()
        for outNode in self.outNodes:
            for inNode in self.inNodes:
                mguExists = mgu(outNode.literal.atom, inNode.literal.atom)!=None
                signsAreDifferent = outNode.literal.negative != inNode.literal.negative
                if mguExists and signsAreDifferent:
                    betweenClauseEdges.add(Edge(outNode, inNode))
        return betweenClauseEdges

    def getClauses(self) -> set[Clause]:
        clauses = set[Clause]()
        for node in self.getAllNodes():
            clauses.add(node.clause)
        return clauses

    def getAllNodes(self) -> set[Node]:
        return self.outNodes.union(self.inNodes)

    def toMermaid(self) -> str:
        output: str = "flowchart TD"

        nodeGroups = defaultdict(list)
        for node in list(self.getAllNodes()):
            nodeGroups[node.clause].append(node)
        nodeGroups: list = list(nodeGroups.values())
        for nodeGroup in nodeGroups:
            nodeGroup = list(nodeGroup)
            groupOutput = f'\n\tsubgraph {nodeGroup[0].clause.name}'
            for node in nodeGroup:
                groupOutput+=f'\n\t\t{node.getIdentifier()}["{node.literal},{node.direction}"]'
            groupOutput+="\n\tend"
            output+=groupOutput

        for edge in self.edges:
            output += f"\n\t{edge.node1.getIdentifier()} --- {edge.node2.getIdentifier()}"

        nodeStrings = list(map(lambda node: node.getIdentifier(), self.getAllNodes()))

        for index, string in enumerate(nodeStrings):
            output = output.replace(string, str(index))
        return output