fib: [int] = None


def f(x: int) -> int:
    res: int = 0
    if fib[x] != -1:
        return fib[x]
    else:
        res = f(x - 1) + f(x - 2)
        fib[x] = res
        return res


def range(len: int) -> [int]:
    i: int = 0
    ret: [int] = None
    ret = []
    while i < len:
        ret = ret + [i]
        i = i + 1
    return ret


def init(len: int, val: int) -> [int]:
    i: int = 0
    ret: [int] = None
    ret = []
    while i < len:
        ret = ret + [val]
        i = i + 1
    return ret


fib = init(200, -1)
fib[0] = 0
fib[1] = 1
print(f(42))
