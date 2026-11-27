"""Compare the four sets in Momihara--Suda--Xiang, Theorem 4.1, with two Paley blocks."""
from check_projective import eligible
from check_trace import Field


def verify(q):
    field = Field(q)
    squares = {field.mul(t, t) for t in range(1, q)}
    nonsquares = set(range(1, q)) - squares
    omega = field.exp[1]
    assert omega in nonsquares and field.char[field.sub(0, 1)] == 1
    matrix = field.matrix()
    incidences = 0
    for i, coset in enumerate((squares, nonsquares)):
        translated = {field.add(t, 1) for t in coset}
        within = translated & squares
        mixed = {field.mul(omega, t) for t in translated} & squares
        sign = (-1)**i
        for y in squares:
            omega_y = field.mul(omega, y)
            inverse = field.inv(y)
            for x in squares:
                ratio = field.mul(x, inverse)
                assert (ratio in within) == (matrix[y][x] == sign), (q, i, x, y)
                assert (ratio in mixed) == (matrix[omega_y][x] == -sign), (q, i, x, y)
                incidences += 2
    return incidences


def main():
    fields = [q for q in eligible() if q < 169]
    count = sum(verify(q) for q in fields)
    print(f"Verified {count} support equivalences over {len(fields)} finite fields "
          f"for the two finite blocks of Theorem 4.1.")


if __name__ == "__main__":
    main()
