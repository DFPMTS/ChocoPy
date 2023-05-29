def g() -> int:
    return 10


def f():
    x: int = 20

    def g(y: int) -> int:
        return x * y

    def h():
        print(g(x))

    h()


f()
