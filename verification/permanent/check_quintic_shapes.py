"""Classify full-line subboards and reproduce four integral Hessian minors."""
import argparse
from pathlib import Path

from check_quintic_discriminant import OPTIONS, coordinate, independent_minor, inverse_certificate, matrix_def, support_text
from check_quintic_endpoint import derivatives
from check_quintic_line_cover import COLUMN, MIXED, PERMUTATIONS, ROW, STRIP, board_order, canonical, moved
from check_quintic_restricted import vector

ROOT = Path(__file__).resolve().parent
PATTERNS = tuple(map(frozenset, (
    (0, 1, 2, 8, 14),
    (0, 1, 2, 5, 6, 8, 14),
    (0, 1, 2, 5, 6, 8, 10, 11, 14),
    (1, 2, 3, 9, 10, 15, 20),
)))
RANKS = (6, 8, 10, 9)
FIRST = tuple(range(5))
SURVIVORS = tuple(canonical(frozenset(board))[0] for board in (
    FIRST, FIRST+(5,), FIRST+(5,6), FIRST+(5,10), FIRST+(5,6,7),
    FIRST+(5,10,15), FIRST+(5,6,7,8), FIRST+(5,10,15,20), tuple(range(10)),
    FIRST+(5,6,7,10,11,12), (0,1,2,3,5,6,7,8,10,15,20), tuple(range(15)),
))


def has_line(board):
    return any(line <= board for line in ROW + COLUMN)


def graph():
    stack = [canonical(STRIP)[0], canonical(MIXED)[0]]
    nodes = {}
    while stack:
        board = stack.pop()
        if board in nodes:
            continue
        children = {}
        for x in sorted(board):
            smaller = board - {x}
            if has_line(smaller):
                child, action = canonical(smaller)
                assert moved(smaller, action) == child
                children[x] = (child, action)
                stack.append(child)
        nodes[board] = children
    return nodes


def pattern_orbit(pattern):
    images = {}
    for flip in (False, True):
        for r in PERMUTATIONS:
            for c in PERMUTATIONS:
                action = (flip, r, c)
                cells = moved(pattern, action)
                images.setdefault(cells, action)
    return images


def labelled_nodes(nodes):
    orbits = [pattern_orbit(p) for p in PATTERNS]
    labels = {}
    for board in nodes:
        if board in SURVIVORS:
            labels[board] = ("allowed", SURVIVORS.index(board))
            continue
        for k, images in enumerate(orbits):
            if len(board) > RANKS[k]+4:
                continue
            match = next((action for cells, action in images.items() if cells <= board), None)
            if match is not None:
                labels[board] = ("rank", k, match)
                break
        else:
            raise AssertionError(f"No rank or shape certificate for {sorted(board)}")
    assert len(nodes) == 58 and len(SURVIVORS) == len(set(SURVIVORS)) == 12
    assert all(board in nodes for board in SURVIVORS)
    return labels


def board_table(nodes):
    boards = sorted(nodes,key=board_order)
    text = """import PermanentWitnesses

/-! The full-line deletion catalogue, the twelve possible pivot shapes at
size twenty-one, and their four ambient Hessian obstructions. -/

namespace PermanentFive
"""
    for name, data in (("shapeBoard",boards),("shapeModel",SURVIVORS),("shapePattern",PATTERNS)):
        elems = ",\n    ".join(support_text(sorted(b)) for b in data)
        text += f"def {name} : Fin {len(data)} → Finset Cell :=\n  ![\n    {elems}]\n\n"
    text += "def shapeRank : Fin 4 → ℕ := "+vector(map(str,RANKS))+"\n\nend PermanentFive\n"
    return text


def minor_certificate(i):
    board, n = PATTERNS[i], RANKS[i]
    matrix = derivatives([int(j in board) for j in range(25)])[1]
    rows, cols = independent_minor(matrix,n)
    block = [[matrix[a][b] for b in cols] for a in rows]
    det, denominator, inverse = inverse_certificate(block)
    text = f"""import PermanentShapeFamily

/-! A rank-{n} minor at the indicator of the {len(board)}-cell sparse pattern. -/

namespace PermanentFive
open Matrix QuinticPencil
private def rows : Fin {n} → Cell := {vector(map(coordinate,rows))}
private def cols : Fin {n} → Cell := {vector(map(coordinate,cols))}
"""
    text += matrix_def("block",block) + matrix_def("inverseNumerator",inverse)
    text += f"""
{OPTIONS}private theorem entries : ∀ i j : Fin {n},
    secondAt (boardPoint (shapePattern {i})) (rows i) (cols j) = block i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

{OPTIONS}private theorem inverse_check : block * inverseNumerator = ({denominator} : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem shape_minor_{i} (K : Type*) [Field K] [CharZero K] :
    AmbientWitness K (shapePattern {i}) (shapeRank {i}) :=
  ambient_of_integer_minor K _ rows cols block entries
    (det_ne_zero_of_inverse_certificate block inverseNumerator {denominator} (by decide) inverse_check)

#print axioms shape_minor_{i}
end PermanentFive
"""
    print(f"Pattern {i}: {len(board)} cells, rank at least {n}, minor determinant {det}.")
    return text


def main():
    from make_shape_graph import graph_source
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-lean",action="store_true")
    opts = parser.parse_args()
    nodes = graph()
    labels = labelled_nodes(nodes)
    files = {"PermanentShapeBoards":board_table(nodes)}
    files.update({f"PermanentShapeMinor{i}":minor_certificate(i) for i in range(4)})
    files["PermanentShapeGraph"] = graph_source(nodes,labels)
    for name, text in files.items():
        path = ROOT / (name+".lean")
        if opts.write_lean:
            path.write_text(text,encoding="utf8")
        else:
            assert path.read_text(encoding="utf8") == text, name
    kept = sum(len(ch) for ch in nodes.values())
    deleted = sum(map(len,nodes)) - kept
    print(f"Verified {len(nodes)} boards, {kept} relabelled deletions, "
          f"{deleted} deletions without a full line, and {len(SURVIVORS)} allowed shapes.")


if __name__ == "__main__":
    main()
