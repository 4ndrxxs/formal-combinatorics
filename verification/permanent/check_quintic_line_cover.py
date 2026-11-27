"""Reproduce the deletion graph for boards without a complete row or column.

The graph starts from three rows and from two rows together with one column.
Every edge carries an explicit row and column relabelling, optionally after
transposition. Its terminal obstructions use exact integer arithmetic.
"""
import argparse
import json
from functools import lru_cache
from itertools import combinations, permutations
from pathlib import Path

from check_quintic_discriminant import ambient_certificate, jet_certificate, support_text
from check_quintic_restricted import vector
from make_line_deletions import deletion_source

ROOT = Path(__file__).resolve().parent
PERMUTATIONS = tuple(permutations(range(5)))
ROW = tuple(frozenset(5*r+c for c in range(5)) for r in range(5))
COLUMN = tuple(frozenset(5*r+c for r in range(5)) for c in range(5))
STRIP = ROW[0] | ROW[1] | ROW[2]
MIXED = ROW[0] | ROW[1] | COLUMN[0]
IDENTITY = tuple(range(5))
COLUMN_MASKS = tuple(tuple(sum(1 << (4-p[c]) for c in range(5) if mask & (1 << (4-c)))
                           for mask in range(32)) for p in PERMUTATIONS)


def transpose(board):
    return frozenset(5*(a%5)+a//5 for a in board)


def moved(board, action):
    flip, rows, columns = action
    oriented = transpose(board) if flip else board
    return frozenset(5*rows[a//5]+columns[a%5] for a in oriented)


@lru_cache(None)
def canonical(board):
    best = None
    for flip, oriented in enumerate((board, transpose(board))):
        masks = tuple(sum(1 << (4-a%5) for a in oriented if a//5 == r) for r in range(5))
        for columns, table in zip(PERMUTATIONS, COLUMN_MASKS):
            rearranged = tuple(table[m] for m in masks)
            order = tuple(sorted(range(5), key=rearranged.__getitem__, reverse=True))
            score = tuple(rearranged[r] for r in order)
            if best is None or score > best:
                best = score
                action = (flip,tuple(order.index(i) for i in range(5)),columns)
    return moved(board,action),action


def folds_to_rectangle(board):
    for oriented in (board,transpose(board)):
        rows = {a//5 for a in oriented}
        if len(rows) <= 3 and any(all(5*r+i not in oriented or 5*r+j not in oriented for r in rows)
                                  for i,j in combinations(range(5),2)):
            return True
    return False


def deletion_graph():
    stack = [canonical(STRIP)[0],canonical(MIXED)[0]]
    nodes = {}
    while stack:
        board = stack.pop()
        if board in nodes:
            continue
        line = next((i for i,cells in enumerate(ROW+COLUMN) if cells <= board),None)
        if folds_to_rectangle(board):
            kind, deletions = "witt", ()
        elif line is not None:
            kind, deletions = "line", (ROW+COLUMN)[line]
        elif len(board) == 10:
            kind, deletions = "ten", ()
        else:
            assert 10 < len(board) <= 12
            kind, deletions = "ambient", board
        children = {i:canonical(board-{i}) for i in sorted(deletions)}
        for i,(child,action) in children.items():
            assert moved(board-{i},action) == child and len(child)+1 == len(board)
            stack.append(child)
        nodes[board] = kind,line,children
    return nodes


def find_embedding(board, targets):
    for flip,oriented in enumerate((board,transpose(board))):
        for rows in PERMUTATIONS:
            row_image = [(rows[a//5],a%5) for a in oriented]
            if max(r for r,_ in row_image)>=3:
                continue
            for cols in PERMUTATIONS:
                image = {5*r+cols[c] for r,c in row_image}
                for i,t in enumerate(targets):
                    if image <= t:
                        action = flip,rows,cols
                        assert moved(board,action) <= t
                        return i,action
    raise ValueError(board)


def board_order(board):
    return len(board),tuple(sorted(board))


def catalogue(nodes):
    boards = sorted(nodes,key=board_order)
    ten = [b for b in boards if nodes[b][0]=="ten"]
    ambient = [b for b in boards if nodes[b][0]=="ambient"]
    assert len(ten)==10 and len(ambient)==4
    src = """import PermanentWitnesses

/-! The representatives in the deletion graph for the full-line obstruction. -/

namespace PermanentFive
"""
    src+=f"def lineBoard : Fin {len(boards)} → Finset Cell :=\n  ![\n    "
    src+=",\n    ".join(support_text(sorted(b)) for b in boards)+"]\n\n"
    for label,subset in (("lineTen",ten),("lineAmbient",ambient)):
        src+=f"def {label} : Fin {len(subset)} → Finset Cell :=\n  "
        src+=vector(f"lineBoard {boards.index(b)}" for b in subset)+"\n\n"
    return boards,ten,ambient,src+"end PermanentFive\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-lean",action="store_true")
    options=parser.parse_args()
    nodes=deletion_graph()
    boards,ten,ambient,catalogue_src=catalogue(nodes)
    data=json.loads((ROOT/"line-ten-data.json").read_text(encoding="utf8"))
    assert [set(d["cells"]) for d in data] == ten
    modules=[("PermanentLineBoards",catalogue_src),
             ("PermanentLineDeletions",deletion_source(nodes,boards,ten,ambient,find_embedding,STRIP,MIXED))]
    modules.extend(jet_certificate(i,d,line_cover=True) for i,d in enumerate(data))
    modules.extend(ambient_certificate(i,b,line_cover=True) for i,b in enumerate(ambient))
    if options.write_lean:
        for name,src in modules:
            (ROOT/(name+".lean")).write_text(src,encoding="utf8")
    print(f"Checked {len(boards)} boards and {sum(len(ch) for _,_,ch in nodes.values())} deletions.")


if __name__ == "__main__":
    main()
