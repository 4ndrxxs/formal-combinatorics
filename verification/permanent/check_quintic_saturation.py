"""Check the quintic cancellation as an exact identity in noncommuting words."""

from collections import Counter
from itertools import product


def words(length, s_degree, t_degree):
    """Expand b(y+s w) D(y+s w+t z)^length c(y+s w) after lifting w."""
    end = [(0, 0, ""), (1, 0, "Z")]
    middle = [(0, 0, "Y"), (1, 0, "W"), (0, 1, "Z")]
    result = Counter()
    for factors in product(end, *([middle] * length), end):
        if sum(a for a, _, _ in factors) == s_degree and sum(b for _, b, _ in factors) == t_degree:
            result["".join(word for _, _, word in factors)] += 1
    return result


def main():
    quartic = words(2, 1, 1)
    cubic = words(1, 2, 0)
    second = words(3, 0, 2)
    assert quartic == cubic + second
    assert second == Counter({"ZZY": 1, "ZYZ": 1, "YZZ": 1})
    assert not words(3, 0, 4)
    print("The quartic coefficient equals the cubic coefficient plus ZZY + ZYZ + YZZ.")
    print("The t^4 coefficient is empty. Both identities hold integrally in the free associative algebra.")


if __name__ == "__main__":
    main()
