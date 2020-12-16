class BTree(object):
    def __init__(self, degree):
        self.degree = degree
        self.root = Node(True)

    def getBest(self, node=False):
        if not node:
            node = self.root
        if node.leaf:
            return node.data[0][1], node.data[0][2]
        else:
            return self.getBest(node.children[0])

    def insert(self, clause, count, evaluation):
        pass

    def remove(self, clause_id):
        pass

class Node(object):
    def __init__(self, leaf=False):
        self.data = []
        self.children = []
        self.leaf = leaf
