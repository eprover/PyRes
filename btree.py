# Deleting a key on a B-tree in Python


# Btree node
import math


class BTreeNode:
    def __init__(self, leaf=False, parent=None):
        self.parent = parent
        self.leaf = leaf
        self.clauses = []
        self.child = []


def sort_node(node):
    node.clauses = sorted(node.clauses, key=lambda clause: clause[0])
    # if not node.leaf:
    #    node.child = sorted(node.child,key=lambda child: child.clauses[0])


class BTree:
    def __init__(self, degree):
        self.root = BTreeNode(True)
        self.degree = degree
        self.min_keys = math.ceil((degree / 2) - 1)
        self.max_keys = degree - 1
        self.split_position = math.floor(self.max_keys / 2) + 1

    # Insert a Clause
    def insert(self, clause, count, evaluation):
        #(evaluation)
        inserted, node = self.addClause(clause, count, evaluation)
        clause = [evaluation, Clause(clause, count)]
        if not inserted:
            self.insert_clause(clause, node)

    def insert_clause(self, clause, node):
        node.clauses.append(clause)
        sort_node(node)
        if len(node.clauses) > self.max_keys:
            self.split_node(node)
        #self.print_tree(self.root)
        # if node is None:
        #    node = self.root
        # if node.leaf:
        #    node.clauses.append(clause)
        #    sort_node(node)
        #    if len(node.clauses) > self.max_keys:
        #        self.split_node(node, parent)
        #    self.print_tree(self.root)
        # else:
        #    for i, clauses in enumerate(node.clauses):
        #        if node.clauses[i][0] > clause[0]:
        #            self.insert_clause(clause, node.child[i], node)
        #            return
        #    self.insert_clause(clause, node.child[-1], node)

    def split_node(self, node):
        root = False
        if node == self.root:
            root = True
            parent = BTreeNode(False)
            self.root = parent
            node.parent = parent
        else:
            parent = node.parent
        clauses = node.clauses
        parent.clauses.append(node.clauses[self.split_position])
        node.clauses = clauses[:self.split_position]
        new_right = BTreeNode(node.leaf, parent)
        new_right.clauses = clauses[self.split_position + 1:]
        if not node.leaf:
            childs = node.child
            node.child = childs[:self.split_position + 1]
            new_right.child = childs[self.split_position + 1:]
            for child in new_right.child:
                child.parent = new_right
        if root:
            parent.child = [node, new_right]
        else:
            parent.child.append(new_right)
            sort_node(parent)
            if len(parent.clauses) > self.max_keys:
                self.split_node(parent)
        #print(parent.child[1].clauses)

    def addClause(self, clause, count, evaluation, node=None):
        if node is None:
            node = self.root
        i = 0
        while i < len(node.clauses) and evaluation > node.clauses[i][0]:
            i += 1
        if i < len(node.clauses) and evaluation == node.clauses[i][0]:
            node.clauses[i][1].backup_clauses.append((clause, count))
            return True, None
        elif node.leaf:
            return False, node
        else:
            return self.addClause(clause, count, evaluation, node.child[i])

    def getBest(self, node=False):
        if not node:
            node = self.root
            if not node.clauses:
                return None, None, True
        if node.leaf:
            if not node.clauses[0][1].backup_clauses:
                best = node.clauses[0][1]
                empty = self.delete_best(node)
            else:
                best = node.clauses[0][1]
                node.clauses[0][1].popClause()
                empty = False
            return best.clause, best.count, empty
        else:
            return self.getBest(node.child[0])

    def debug(self):
        node = self.root
        if node.leaf:
            #print("Root")
            return
        while True:
            #print("Next")
            #print(len(node.child) - len(node.clauses))
            node = node.child[0]
            if node.leaf:
                break

    def delete_best(self, node):
        if node == self.root:
            return self.delete_best_from_root()
        elif len(node.clauses) == self.min_keys:
            return self.delete_best_underflow(node)
        else:
            node.clauses.pop(0)
            return False

    def delete_best_from_root(self):
        self.root.clauses.pop(0)
        return False

    def delete_best_underflow(self, node):
        if len(node.parent.child[1].clauses) > self.min_keys:
            right_clause = node.parent.child[1].clauses.pop(0)
            upper_clause = node.parent.clauses[0]
            node.parent.clauses[0] = right_clause
            node.clauses.append(upper_clause)
            node.clauses.pop(0)
            return False
        else:
            return self.merge(node.parent, True)
        # if node is None:
        #    node = self.root
        # if node.child[0].leaf:
        #    print("Hier", len(node.child))
        #    if len(node.child[1].clauses) > self.min_keys:
        #        right_clause = node.child[1].clauses.pop(0)
        #        upper_clause = node.clauses[0]
        #        node.clauses[0] = right_clause
        #        node.child[0].clauses.append(upper_clause)
        #        node.child[0].clauses.pop(0)
        #        return False
        #    else:
        #        return self.delete_best_merge(node)

        # else:
        #    return self.delete_best_underflow(node.child[0], node)

    def merge(self, node, delete=False):
        if not delete:
            childs = node.child[0].child + node.child[1].child
        new_node = BTreeNode(node.child[0].leaf, node)
        new_node.clauses = node.child[0].clauses + [node.clauses[0]] + node.child[1].clauses
        node.child.pop(0)
        node.clauses.pop(0)
        node.child[0] = new_node
        if delete:
            node.child[0].clauses.pop(0)
        else:
            new_node.child = childs
            for child in childs:
                child.parent = new_node

        if len(node.clauses) >= self.min_keys:
            return False
        elif node == self.root:
            if not node.clauses:
                self.root = node.child[0]
                self.root.parent = None
            return False
        elif len(node.parent.child[1].clauses) > self.min_keys:
            node.clauses.append(node.parent.clauses[0])
            node.child.append(node.parent.child[1].child.pop(0))
            node.parent.clauses.append(node.parent.child[1].clauses.pop(0))
            return False
        else:
            return self.merge(node.parent)

        #elif not node == self.root:
        #    if len(node.parent.child[1].clauses) > self.min_keys:
        #        pass
        #        # TODO: borrow and return False
        #    else:
        #        self.merge(node.parent)
        #        # TODO: Recursive till root than return 0?
        #return False
        #    new_node = BTreeNode(True)
        #    new_node.clauses = node.child[0].clauses + [node.clauses[0]] + node.child[1].clauses
        #    node.child.pop(0)
        #    node.clauses.pop(0)
        #    node.child[0] = new_node
        #    node.child[0].clauses.pop(0)
        #   if node.clauses >= self.min_keys:
        #       return False
        #   else:

    # def delete_best_merge_node(self, node, parent=None):
    #    if node == self.root:
    #        new_node = BTreeNode(True)
    #        new_node.clauses = node.child[0].clauses + [node.clauses[0]] + node.child[1].clauses
    #        node.child.pop(0)
    #        node.child[0] = new_node
    #        return False
    #   else:
    #        pass

    # Print the tree
    def print_tree(self, node, l=0):
        #if not node == self.root:
        #    print("Parent: ", node.parent.clauses[0])
        print("Level ", l, " ", len(node.clauses), end=":")
        for i in node.clauses:
            print(i, end=" ")
        print()
        l += 1
        if len(node.child) > 0:
            for i in node.child:
                self.print_tree(i, l)


class Clause:
    def __init__(self, clause, count):
        self.clause = clause
        self.count = count
        self.backup_clauses = []

    def popClause(self):
        self.clause = self.backup_clauses[0][0]
        self.count = self.backup_clauses[0][1]
        self.backup_clauses.pop(0)
