"""Verify the degree-fifteen Hessian-block restriction using integer arithmetic."""

from itertools import permutations

BASE = [[1,1,1,1,1],[1,-1,1,1,1],[1,1,-1,-1,0]]
SLOPE = [[-1,-1,-2,0,1],[1,1,-2,0,1],[0,0,-2,1,2]]
P = [-3,7,-25,61,149,-79,-696,782,-433,-743,1318,-548,-82,164,-24,-16]
Q = [-6,23,-27,57,-25,-31,1,-282,164,-201,329,-54,-52,8]
BEZOUT_U = [21701154399483022149877100307075, -8644630554419955003303595173610, 180402427740258950488189477374803, -61911369117968301304330676985312, -1168555340304340093149567550611509, -1665574683847488368168793754440156, 1917881247280603171182247979707428, -2031236913787334387238519885511298, -785849413994989444963513695616509, 3924935355084502817894088752330132, -2095349161880612382114378026301498, -18988972748486657260822392329122, 559693659860653532720965297464212, -123844240179646663375562464022392, -61057830297938146743610834204400]
BEZOUT_V = [-45908883176378592158529606044934, 76544050759993031452429211929949, -61213934416612747307185542299960, 282851398266142525851732921877889, 340101284298082009133497016330166, 407279989711347122297155521180971, 791084837267996908095235466992214, -534794439511678318481096972569088, 193510350664653730717483123938580, -1093934613143010769677356347867597, 302025605839892782599748539737574, 182309201101929255286662104806404, -30528915148969073371805417102200]
BEZOUT_CONSTANT = 7519723132237643576326216292352

def add(left, right):
    result = left.copy()
    for monomial, coefficient in right.items():
        result[monomial] = result.get(monomial, 0) + coefficient
    return {m: c for m, c in result.items() if c}


def multiply(left, right):
    result = {}
    for (a, b), c in left.items():
        for (i, j), d in right.items():
            exponent = (a + i, b + j)
            result[exponent] = result.get(exponent, 0) + c * d
    return {m: c for m, c in result.items() if c}


def scale(polynomial, scalar):
    return {m: scalar * c for m, c in polynomial.items() if scalar * c}


def permutation_sum(matrix, signed):
    dimension = len(matrix)
    result = {}
    for order in permutations(range(dimension)):
        inversions = sum(order[i] > order[j] for i in range(dimension)
                         for j in range(i + 1, dimension))
        term = {(0, 0): -1 if signed and inversions % 2 else 1}
        for i, j in enumerate(order):
            term = multiply(term, matrix[i][j])
        result = add(result, term)
    return result


def univariate(coefficients):
    return {(i, 0): value for i, value in enumerate(coefficients) if value}


def main():
    matrix = [[{(0, 0): b, (1, 0): s} for b, s in zip(row, direction)]
              for row, direction in zip(BASE, SLOPE)]
    matrix[2][0][(0, 1)] = 1
    block = []
    for j in range(5):
        entries = []
        for k in range(5):
            if j == k:
                entries.append({})
                continue
            surviving = [c for c in range(5) if c not in (j, k)]
            minor = [[row[c] for c in surviving] for row in matrix]
            entries.append(permutation_sum(minor, signed=False))
        block.append(entries)
    determinant = permutation_sum(block, signed=True)
    pencil = add(univariate(P), multiply({(0, 1): 1}, univariate(Q)))
    assert determinant == scale(pencil, 64)
    assert determinant[(15, 0)] == -1024
    assert max(i for i, _ in univariate(P)) == 15
    assert max(i for i, _ in univariate(Q)) == 13
    bezout = add(multiply(univariate(BEZOUT_U), univariate(Q)),
                 multiply(univariate(BEZOUT_V), univariate(P)))
    assert bezout == {(0, 0): BEZOUT_CONSTANT} and BEZOUT_CONSTANT != 0
    print("Exact complementary cubics, degree-fifteen determinant, and integer Bezout identity passed.")


if __name__ == "__main__":
    main()
