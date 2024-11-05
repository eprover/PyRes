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
        return f"{self.literal}{self.clause.name}{self.direction}"

    def __repr__(self) -> str:
        return f"<{self.clause.name},{self.literal},{self.direction}>"

class Edge():
    def __init__(self, node1: Node, node2: Node) -> None:
        self.node1: Node = node1
        self.node2: Node = node2

    def __repr__(self) -> str:
        return f"Edge: {self.node1} - {self.node2}"


class RelevanceGraph():
    def __init__(self, clauseSet: ClauseSet) -> None:
        self.outNodes, self.inNodes = self.constructNodes(clauseSet)
        self.edges: set[Edge] = self.constructInClauseEdges().union(self.constructBetweenClauseEdges())

    @staticmethod
    def constructNodes(clauseSet: ClauseSet) -> tuple[set[Node]]:
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

    def getAllNodes(self) -> set[Node]:
        return self.outNodes.union(self.inNodes)

    @staticmethod
    def nodesToClauses(nodes: set[Node]) -> ClauseSet:
        clauses = ClauseSet()
        for node in nodes:
            clauses.addClause(node.clause)
        clauses.clauses = list(set(clauses.clauses))
        return clauses

    def clausesToNodes(self, clauses: ClauseSet) -> set[Node]:
        allNodes = self.getAllNodes()
        nodesOfClauseSubset = filter(lambda node: clauses.clauses.__contains__(node.clause), allNodes)
        return nodesOfClauseSubset

    @staticmethod
    def isNeighbouringEdgeOfSubset(edge: Edge, subset: list[Node]) -> bool:
        containsFirst = subset.__contains__(edge.node1)
        containsSecond = subset.__contains__(edge.node2)
        return containsFirst and not containsSecond or containsSecond and not containsFirst

    def getNeighbours(self, subset: list[Node]) -> list[Node]:
        neighbouringNodes: list[Node] = []
        neighbouringEdges: list[Edge] = filter(lambda edge: self.isNeighbouringEdgeOfSubset(edge, subset), self.edges)

        for edge in neighbouringEdges:
            if subset.__contains__(edge.node1.clause):
                neighbouringNodes.append(edge.node2)
            else:
                neighbouringNodes.append(edge.node1)
        return neighbouringNodes

    def getRelevantNeighbourhood(self, fromClauses: ClauseSet, distance: int) -> ClauseSet:

        neighbourhood: list[Node] = list(self.clausesToNodes(fromClauses))
        for _ in range(2*distance-1):
            newNeighbours = self.getNeighbours(neighbourhood)
            neighbourhood += newNeighbours

        clauses = self.nodesToClauses(neighbourhood)
        return clauses

    def toMermaid(self) -> str:
        output: str = "flowchart TD"

        nodeGroups = defaultdict(list)

        nodesList: list[Node] = list(self.getAllNodes())
        nodesSorted = sorted(nodesList, key=lambda node: (-len(node.clause.literals), node.clause.name.casefold(), node.literal.__repr__().casefold(), node.direction.casefold()))
        for node in nodesSorted:
            nodeGroups[node.clause].append(node)
        nodeGroups: list = list(nodeGroups.values())
        for nodeGroup in nodeGroups:
            nodeGroup = list(nodeGroup)
            groupOutput = f'\n\tsubgraph {nodeGroup[0].clause.name}'
            for node in nodeGroup:
                groupOutput+=f'\n\t\t{node.getIdentifier()}["{node.literal},{node.direction}"]'
            groupOutput+="\n\tend"
            output+=groupOutput

        # Edges for keeping same literals in clause together
        output += "\n\t%% invisible edges (for better visualization)"
        for index, _ in enumerate(self.inNodes):
            output += f"\n\t{2*index} ~~~ {2*index+1}"

        # edgesSorted = sorted(list(self.edges), key=lambda edge: (edge.node1.clause.name.casefold(), edge.node1.literal.__repr__().casefold(), edge.node1.direction.casefold()))
        edgesSorted = sorted(
            list(self.edges),
            key = lambda edge: (
                edge.node1.clause != edge.node2.clause,
                nodesSorted.index(edge.node1),
                nodesSorted.index(edge.node2),
                edge.node1.clause.name.casefold(),
                edge.node1.literal.__repr__().casefold(),
                edge.node1.direction.casefold(),
            ),
        )
        currentEdgeType: str = "in-clause"
        output += "\n\t%% in-clause edges"
        directionFits: bool = True
        for edge in edgesSorted:
            if currentEdgeType=="in-clause":
                if edge.node1.clause != edge.node2.clause:
                    currentEdgeType = "between-clause"
                    output += "\n\t%% between-clause edges"
                if directionFits:
                    output += (f"\n\t{edge.node1.getIdentifier()} --- {edge.node2.getIdentifier()}")
                else:
                    output += (f"\n\t{edge.node2.getIdentifier()} --- {edge.node1.getIdentifier()}")
                directionFits = not directionFits
            if currentEdgeType=="between-clause":
                output += (f"\n\t{edge.node1.getIdentifier()} --- {edge.node2.getIdentifier()}")

        nodeStrings = list(map(lambda node: node.getIdentifier(), nodesSorted))

        for index, string in enumerate(nodeStrings):
            output = output.replace(string, str(index))
        return output
