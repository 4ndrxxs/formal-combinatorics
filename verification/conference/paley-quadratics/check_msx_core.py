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
    bit_rows = [[], []]
    coordinates = sorted(squares)
    for i, coset in enumerate((squares, nonsquares)):
        shifted = {field.add(t, 1) for t in coset}
        first = shifted & squares
        second = {field.mul(omega, t) for t in shifted} & squares
        rows = []
        for y in coordinates:
            xs = [field.mul(x, field.inv(y)) for x in coordinates]
            rows.append(tuple(sum(1 << k for k, x in enumerate(xs) if x in support)
                              for support in (first, second)))
        for col in (0, 1):
            bit_rows[col].append([row[col] for row in rows])
    inner_products = 0
    for i, first_rows in enumerate(bit_rows[0]):
        for second_rows in bit_rows[1]:
            for a, y in enumerate(coordinates):
                for b, z in enumerate(coordinates):
                    distance = ((first_rows[a] ^ first_rows[b]).bit_count()
                                + (second_rows[a] ^ second_rows[b]).bit_count())
                    observed = 2*len(coordinates)-2*distance
                    expected = q-1 if y == z else -2-2*((-1)**i)*field.char[field.sub(z, y)]
                    assert observed == expected, (q, i, a, b, observed, expected)
                    inner_products += 1
    return incidences, inner_products


def main():
    fields = [q for q in eligible() if q < 169]
    checked = [verify(q) for q in fields]
    incidences, products = map(sum, zip(*checked))
    print(f"Verified {incidences} support equivalences and {products} exact row inner products "
          f"for the four signed block pairs in Theorem 4.1 over {len(fields)} finite fields.")


if __name__ == "__main__":
    main()
