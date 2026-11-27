"""Exact finite checks for the Hessian and cover steps in the quintic working proof."""
from fractions import Fraction
from itertools import combinations, permutations
from math import prod

ORDER = 5
CELLS = list(range(ORDER * ORDER))
TERMS = [tuple(ORDER*i+j for i,j in enumerate(p)) for p in permutations(range(ORDER))]


def derivatives(values):
    first = [0] * len(CELLS)
    hessian = [[0] * len(CELLS) for _ in CELLS]
    for term in TERMS:
        for x in term:
            first[x] += prod(values[i] for i in term if i != x)
            for y in term:
                if x != y:
                    hessian[x][y] += prod(values[i] for i in term if i != x and i != y)
    return first, hessian


def rank(matrix):
    a = [list(map(Fraction, row)) for row in matrix]
    pivot = 0
    for col in range(len(a[0])):
        row = next((i for i in range(pivot,len(a)) if a[i][col]), None)
        if row is None:
            continue
        a[pivot], a[row] = a[row], a[pivot]
        for i in range(pivot+1,len(a)):
            if a[i][col]:
                s = a[i][col] / a[pivot][col]
                a[i] = [x - s*y for x,y in zip(a[i],a[pivot])]
        pivot += 1
    return pivot


def cover_support(vertices):
    return {x for x in CELLS if x//ORDER in vertices or ORDER+x%ORDER in vertices}


def indicators(support):
    return [int(x in support) for x in CELLS]


def main():
    extremal = []
    for size in (2,3):
        covers = [(vertices,cover_support(vertices)) for vertices in combinations(range(2*ORDER),size)]
        largest = max(len(s) for _,s in covers)
        assert largest == size*ORDER
        print(f"All {len(covers)} vertex covers of size {size} cover at most {largest} cells.")
        if size==3:
            extremal = [s for _,s in covers if len(s)==largest]
    assert len(extremal)==20
    for supp in extremal:
        grad, hessian = derivatives(indicators(supp))
        assert not any(grad) and rank(hessian)==10
    near_extremal = {frozenset(supp - {cell}) for supp in extremal for cell in supp}
    assert len(near_extremal) == 300
    for supp in near_extremal:
        grad, hessian = derivatives(indicators(supp))
        assert not any(grad) and rank(hessian) == 10
    three = {0,6,12}
    grad, hessian = derivatives(indicators(three))
    outside = [5*i+j for i in (3,4) for j in (3,4)]
    block = [[hessian[i][j] for j in outside] for i in outside]
    assert not any(grad) and block==[[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,0]]
    assert rank(hessian)==4
    grad, _ = derivatives(indicators({0,6,12,18}))
    assert grad[24]==1
    print("Direct differentiation of all 120 permutation monomials: a four-edge matching has gradient entry one; "
          "a three-edge matching has Hessian rank four; all 20 extremal three-line supports have Hessian rank ten.")
    print("All 300 three-line supports with one cell removed have Hessian rank ten at their indicator matrices.")
    print("The checked finite data do not by themselves establish the general affine-pencil reduction.")


if __name__ == "__main__":
    main()
