def f(x1: int, x2: int, x3: int, x4: int, x5: int, x6: int, x7: int, x8:int,x9:int,x: str,y:str) -> str:    
    i:int = 0
    ret:str = ""

    while i <x1+x2+x9:
        ret=ret+x+y
        i=i+1
    return ret

print(f(1, 2, 3, 4, 5, 6, 7, 8,9,"X","y"))