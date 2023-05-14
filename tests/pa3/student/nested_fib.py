def f():
    def fib(n: int) -> int:
        if n == 0 or n == 1:
            return 1
        else:
            return g(n - 1) + g(n - 2)

    def g(n: int) -> int:
        return fib(n)

    print(g(10))


f()
