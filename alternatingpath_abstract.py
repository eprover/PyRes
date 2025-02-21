from abc import ABC, abstractmethod
from clausesets import ClauseSet

class RelevanceGraph(ABC):

    def __init__(self, clause_set: ClauseSet):
        self.construct_graph(clause_set)

    @abstractmethod
    def construct_graph(self, clause_set: ClauseSet):
        pass

    @abstractmethod
    def get_rel_neighbourhood(self, from_clauses: ClauseSet, distance: int):
        pass