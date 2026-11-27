"""Enumerate the 52 one-cell deletions of the thirteen-cell representatives.

The output lists explicit row and column permutations. Lean checks containment
for every remaining cell before the classification can be used in the proof.
"""
import argparse
import json
from itertools import permutations
from pathlib import Path

from check_quintic_discriminant import MIXED, PARENTS, PURE
from check_quintic_restricted import vector

ROOT = Path(__file__).resolve().parent


def swaps_for(p):
    current = list(range(5))
    swaps = []
    for i, target in enumerate(p):
        source = current[i]
        if source == target:
            continue
        moves = {source: target, target: source}
        current = [moves.get(x, x) for x in current]
        swaps.append((source, target))
    assert tuple(current) == p
    return swaps


def permutation_term(p):
    swaps = swaps_for(p)
    if not swaps:
        return "Equiv.refl Idx"
    first, *tail = swaps
    term = f"(Equiv.swap {first[0]} {first[1]})"
    for a, b in tail:
        term = f"({term}.trans (Equiv.swap {a} {b}))"
    return term


def find_layouts():
    records = json.loads((ROOT / "twelve-block-data.json").read_text(encoding="utf8"))
    shapes = {}
    for i, record in enumerate(records):
        strip = PURE if record["cover"] == [3, 0] else MIXED
        shapes[frozenset(strip).difference(record["holes"])] = i
    perms = sorted(permutations(range(5)), key=lambda p: (len(swaps_for(p)), p))
    pairs = sorted(((r, c) for r in perms for c in perms),
                   key=lambda rc: len(swaps_for(rc[0])) + len(swaps_for(rc[1])))
    index_perms = [tuple(range(5))]
    lookup = []
    for parent in PARENTS:
        table = []
        for x in range(25):
            entry = (0, 0, 0)
            if x in parent:
                coords = [divmod(j, 5) for j in parent if j != x]
                for r, c in pairs:
                    image = frozenset(5*r[i] + c[j] for i, j in coords)
                    if image in shapes:
                        for perm in (r, c):
                            if perm not in index_perms:
                                index_perms.append(perm)
                        entry = (shapes[image], index_perms.index(r), index_perms.index(c))
                        break
                else:
                    raise AssertionError(f"unclassified deletion {parent}, {x}")
            table.append(entry)
        lookup.append(table)
    return index_perms, lookup


def layout_source(perms, tables):
    s = """import PermanentTwelveShapes

/-! Each single deletion of a canonical thirteen-cell board is identified
with a twelve-cell representative by two explicit permutations. -/

namespace PermanentFive
open Equiv Finset
"""
    s += f"private def layoutPerm : Fin {len(perms)} → Perm Idx :=\n  "
    s += vector(permutation_term(p) for p in perms) + "\n\n"
    s += f"private def layout : Fin 4 → Idx → Idx → Fin 9 × Fin {len(perms)} × Fin {len(perms)} :=\n  ![\n    "
    s += ",\n    ".join(vector(vector(f"({a},{b},{c})" for a,b,c in table[k:k+5])
                                    for k in range(0,25,5)) for table in tables) + "]\n"
    s += """
set_option maxRecDepth 30000 in
set_option maxHeartbeats 24000000 in
private theorem checked_layout : ∀ t, ∀ x ∈ thirteenShape t, ∀ j ∈ (thirteenShape t).erase x,
    ((layoutPerm (layout t x.1 x.2).2.1).prodCongr
      (layoutPerm (layout t x.1 x.2).2.2)) j ∈ twelveShape (layout t x.1 x.2).1 := by
  intro t
  fin_cases t <;> decide +kernel

theorem twelve_deletion (t : Fin 4) (x : Cell) (hx : x ∈ thirteenShape t) :
    ∃ (i : Fin 9) (r c : Perm Idx),
      ∀ j ∈ (thirteenShape t).erase x, (r.prodCongr c) j ∈ twelveShape i :=
  ⟨_,_,_,checked_layout t x hx⟩

#print axioms twelve_deletion
end PermanentFive
"""
    return s


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-lean", action="store_true")
    args = parser.parse_args()
    p, tables = find_layouts()
    print(f"Checked 52 single deletions, using {len(p)} distinct permutations of five indices.")
    if args.write_lean:
        (ROOT / "PermanentTwelveLayouts.lean").write_text(layout_source(p, tables), encoding="utf8")


if __name__ == "__main__":
    main()
