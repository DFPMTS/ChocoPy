def f():
    def h(x: int) -> int:
        fib_res: int = 0

        def fib(n: int) -> int:
            nonlocal fib_res

            def x_to_x(x: int) -> int:
                if x == 0:
                    return n + x
                else:
                    return x_to_x(x - 1) + n + x

            if n == 0 or n == 1:
                fib_res = x_to_x(x)
                return x_to_x(fib_res)
            else:
                fib_res = fib(n - 1) + fib(n - 2)
                return x_to_x(fib_res)

        return fib(x)

    print(h(3))


f()
