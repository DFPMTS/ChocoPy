class Node(object):
    left: "Node" = None
    right: "Node" = None
    val: int = 0

    def print_in_order(self: "Node"):
        if not self.left is None:
            # print(self.left.val)
            self.left.print_in_order()
        print(self.val)
        if not self.right is None:
            # print(self.right.val)
            self.right.print_in_order()

    def set_value(self: "Node", new_val: int):
        self.val = new_val

    def add_left(self: "Node", x: "Node"):
        self.left = x

    def add_right(self: "Node", x: "Node"):
        self.right = x


x1: Node = None
x2: Node = None
x3: Node = None
x4: Node = None
x5: Node = None

x1 = Node()
x2 = Node()
x3 = Node()
x4 = Node()
x5 = Node()

x1.set_value(1)
x2.set_value(2)
x3.set_value(3)
x4.set_value(4)
x5.set_value(5)

x3.add_left(x1)
x1.add_right(x2)

x3.add_right(x4)
x4.add_right(x5)

x3.print_in_order()
