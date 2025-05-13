import unittest
from alternatingpath_universal_set import UniversalSetRelevanceGraph
from alternatingpath_adjacency_set import AdjacencySetRelevanceGraph
from fofspec import FOFSpec


def load_cnf(problem_path):
    problem = FOFSpec()
    problem.parse(problem_path)
    cnf = problem.clausify()
    return cnf


def compute_neighbourhood(apt_class, problem_path, rel_distance):
    # Load problem
    cnf = load_cnf(problem_path)
    neg_conjs = cnf.getNegatedConjectures()
    # Construct relevance graph
    rel_graph = apt_class(cnf)
    rel_cnf = rel_graph.get_rel_neighbourhood(neg_conjs, rel_distance)
    return rel_cnf


apt_classes = [UniversalSetRelevanceGraph, AdjacencySetRelevanceGraph]

testproblems = [
    ("EXAMPLES/PUZ002-1.p", 0, 1),
    ("EXAMPLES/PUZ002-1.p", 1, 2),
    ("EXAMPLES/PUZ002-1.p", 2, 3),
    ("EXAMPLES/PUZ002-1.p", 3, 4),
    ("EXAMPLES/PUZ002-1.p", 4, 5),
    ("EXAMPLES/PUZ002-1.p", 5, 6),
    ("EXAMPLES/PUZ002-1.p", 6, 7),
    ("EXAMPLES/PUZ002-1.p", 7, 8),
    ("EXAMPLES/PUZ002-1.p", 8, 9),
    ("EXAMPLES/PUZ002-1.p", 9, 10),
    ("EXAMPLES/PUZ002-1.p", 10, 11),
    ("EXAMPLES/PUZ002-1.p", 11, 12),
    ("EXAMPLES/PUZ002-1.p", 12, 12),
    ("EXAMPLES/PUZ002-1.p", 13, 12),
]


class TestClass(unittest.TestCase):

    def test_rel_cnf_size(self):
        """Test, wether the size of the output ClauseSet is right for a given graph_class, problem and rel_distance"""
        print()
        for problem_path, rel_distance, expected in testproblems:
            for apt_class in apt_classes:
                msg = f"Testing '{apt_class.__name__}' on '{problem_path}' with rel_distance {rel_distance}"
                print(msg)
                with self.subTest(msg=msg):
                    rel_cnf_size = len(
                        compute_neighbourhood(apt_class, problem_path, rel_distance)
                    )
                    self.assertEqual(rel_cnf_size, expected)


if __name__ == "__main__":
    unittest.main(verbosity=2)
