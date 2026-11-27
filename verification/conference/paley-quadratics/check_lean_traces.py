"""Generate kernel-checkable Lean theorems for the listed principal blocks.

The generated theorems verify the conference identity on all entries, each
principal block, its integer cubic trace and margin, and a four-fifths lower
bound for the determinant of the complete matrix without additional hypotheses.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from tempfile import TemporaryDirectory

from check_projective import eligible
from check_trace import Field


EXPECTED_SIGNS = {
    'split-squares', 'split-nonsquares', 'nonsplit-negative',
    'split-squares-opposite', 'split-nonsquares-opposite', 'nonsplit-negative-opposite',
}
MODULE = 'Quantum.Hadamard.ConferenceBitCompletion'


def checked_rows(predicate, count, prefix):
    """Give each row its own closed declaration so the kernel can release its reduction cache."""
    proofs = [
        f'private theorem {prefix}{i} : {predicate} {i}=true := by decide +kernel'
        for i in range(count)
    ]
    proofs.extend([
        f'private theorem {prefix}Checked : allBelow {count} {predicate}=true := by',
        f'  have h : allBelow 0 {predicate}=true := rfl',
    ])
    proofs.extend(f'  have h := allBelow_step h {prefix}{i}' for i in range(count))
    proofs.append('  exact h')
    return '\n'.join(proofs)


def source(case):
    q = case['q']
    v = (q+1)//2
    names = [s['signing'] for s in case['signs']]
    if len(names) != 6 or set(names) != EXPECTED_SIGNS:
        raise ValueError(f'Unexpected sign labels at q={q}')
    field = Field(q)
    full = field.matrix()
    expected_sets = field.signs()
    full_words = [sum(1 << j for j, a in enumerate(row) if a == -1) for row in full]
    n = q+1
    k = v-1
    parts = [f'import {MODULE}', 'open Hadamard.BitTrace Hadamard.DeterminantRatio Matrix',
             'set_option maxHeartbeats 12000000', 'set_option maxRecDepth 60000',
             f'namespace PaleyBits{q}']
    parts.append(f"""
def rawFull (i : ℕ) : ℕ := #[{', '.join(map(str,full_words))}][i]!
def fullRows (i : Fin {n}) : ℕ := rawFull i.val

private theorem fullSymmetric : (wordMatrix fullRows).IsSymm := by
  have h : ∀ i j : Fin {n}, sign (fullRows i) j.val=sign (fullRows j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem fullDiagonal : ∀ i : Fin {n}, sign (fullRows i) i.val=1 := by decide +kernel
{checked_rows(f'(lowerRow {n} rawFull)',n,'lower')}

private theorem fullPairs : ∀ i j : Fin {n}, i≠j →
    correlation {n} (fullRows i) (fullRows j)=2*sign (fullRows i) j.val :=
  correlations_of_lower rawFull fullSymmetric lowerChecked
""")
    endpoints = []
    for s in case['signs']:
        tag = ''.join(piece.title() for piece in s['signing'].split('-'))
        ids = s['points']
        words = list(map(int,s['negative_row_bits']))
        if len(words) != v or len(set(ids)) != v or len(ids) != v:
            raise ValueError(f'Incorrect number of points or rows at q={q}')
        if any(w < 0 or w >= 2**v for w in words):
            raise ValueError(f'Row exceeds its width at q={q}')
        if set(ids) != expected_sets[s['signing']]:
            raise ValueError(f"Invalid positive coordinates at q={q}, {s['signing']}")
        outside = sorted(set(range(n))-set(ids))
        position = {point:i for i,point in enumerate(ids+outside)}
        positive = ', '.join(map(str,ids))
        negative = ', '.join(map(str,outside))
        inverse = ', '.join(str(position[i]) for i in range(n))
        encoded = ', '.join(map(str,words))
        row_totals = [sum((v-2*(a^b).bit_count())*(-1 if b & (1 << i) else 1) for b in words)
                      for i, a in enumerate(words)]
        encoded_totals = ', '.join(map(str,row_totals))
        tr, margin = int(s['cubic_trace']), int(s['integer_margin'])
        parts.append(f"""
namespace {tag}
def rawWords (i : ℕ) : ℕ := #[{encoded}][i]!
def words (i : Fin {v}) : ℕ := rawWords i.val
private def rowTotals (i : ℕ) : ℤ := (#[{encoded_totals}]:Array ℤ)[i]!
private def rowAgrees (i : ℕ) : Bool := decide (packedRowTotal {v} rawWords i=rowTotals i)

{checked_rows('rowAgrees',v,'row')}

private theorem symmetric : (wordMatrix words).IsSymm := by
  have h : ∀ i j : Fin {v}, sign (words i) j.val=sign (words j) i.val := by decide +kernel
  ext i j
  exact h j i

private theorem diagonal : ∀ i : Fin {v}, sign (words i) i.val=1 := by decide +kernel
private theorem computed : cubicInteger words=({tr}:ℤ) := by
  change cubicInteger (fun i : Fin {v} ↦ rawWords i.val)=_
  rw [cube_of_totals rawWords rowTotals rowChecked]
  decide +kernel

theorem certificate :
    ((wordMatrix words-1)^3).trace=({tr}:ℤ) ∧
    87*({v}:ℤ)^3+375*{v}*(4*{v}-3)+1000*((wordMatrix words-1)^3).trace-
      1110*{q}*({v}-1)=({margin}:ℤ) ∧ 0≤({margin}:ℤ) := by
  rw [(cubicInteger_eq_trace words symmetric diagonal).symm, computed]
  norm_num

def pointOrder : Fin {v} ⊕ Fin {v} → Fin {n}
  | .inl i => Fin.ofNat {n} (#[{positive}][i.val]!)
  | .inr i => Fin.ofNat {n} (#[{negative}][i.val]!)

def pointPosition (i : Fin {n}) : Fin {v} ⊕ Fin {v} :=
  let j : ℕ := #[{inverse}][i.val]!
  if j<{v} then .inl (Fin.ofNat {v} j) else .inr (Fin.ofNat {v} (j-{v}))

def indexing : (Fin {v} ⊕ Fin {v}) ≃ Fin {n} where
  toFun := pointOrder
  invFun := pointPosition
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem principalRows : ∀ i j : Fin {v},
    sign (fullRows (indexing (Sum.inl i))) (indexing (Sum.inl j)).val=sign (words i) j.val := by
  decide +kernel

theorem determinant_bound : (4/5:ℝ)*((2*{q})*({q}-1)^{k}) ≤
    |(orderedWordBlock fullRows indexing +
      Matrix.diagonal (Sum.elim (fun _ ↦ (1:ℝ)) (fun _ ↦ -1))).det| := by
  have b : (4/5:ℝ)*ewBound {k} ≤
      |(orderedWordBlock fullRows indexing+Matrix.diagonal completionSign).det| := by
    apply explicit_determinant {k} fullRows words indexing (by decide) (by norm_num)
      fullSymmetric fullDiagonal fullPairs principalRows
    dsimp only
    rw [certificate.1]
    norm_num
  have ew : ewBound {k}=(2*{q})*({q}-1)^{k} := by norm_num [ewBound]
  rw [ew] at b
  exact b

#print axioms certificate
#print axioms determinant_bound
end {tag}
""")
        endpoints.extend(f'PaleyBits{q}.{tag}.{t}' for t in ('certificate','determinant_bound'))
    parts.append(f'end PaleyBits{q}')
    return '\n'.join(parts)+'\n', endpoints


def lake_project(folder):
    return next((p for p in (folder,*folder.parents)
                 if (p/'lakefile.toml').is_file() or (p/'lakefile.lean').is_file()), None)


def check(case, root, tmp, lean, checker, env):
    module = f"PaleyBits{case['q']}"
    src = tmp/(module+'.lean')
    code, names = source(case)
    src.write_text(code,encoding='utf8')
    result = subprocess.run([lean,'-R',str(tmp),'-o',str(src.with_suffix('.olean')),str(src)],
                            cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                            encoding='utf8',errors='replace')
    if result.returncode or 'sorryAx' in result.stdout:
        raise RuntimeError(f'{module}\n{result.stdout}')
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",' '.join(result.stdout.split()))
    if set(names) != {name for name,_ in reports}:
        raise RuntimeError(f'Missing kernel endpoint for {module}: {reports}')
    allowed = {'propext','Classical.choice','Quot.sound'}
    if any(set(axioms.split(', '))-allowed for _,axioms in reports):
        raise RuntimeError(f'Unexpected axiom for {module}: {reports}')
    subprocess.run([checker,'-v',module],cwd=tmp,env=env,check=True)
    print(f"{module}: six unconditional determinant bounds and six integer trace certificates verified.",flush=True)


def main():
    folder = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path,default=lake_project(folder))
    parser.add_argument('--q',type=int,help='Check one of the 18 fields.')
    parser.add_argument('--sources',type=Path,help='Keep the generated Lean sources in this directory.')
    parser.add_argument('--jobs',type=int,default=1,help='Number of fields to check concurrently.')
    args = parser.parse_args()
    if args.project is None:
        parser.error('Supply the Lake project with --project.')
    if args.jobs < 1:
        parser.error('--jobs must be positive.')
    root = args.project.resolve()
    exe = '.exe' if os.name == 'nt' else ''
    lake = shutil.which('lake') or str(Path.home()/'.elan'/'bin'/('lake'+exe))
    subprocess.run([lake,'build',MODULE],cwd=root,check=True,stdout=subprocess.DEVNULL)
    probe = 'import os,json; print(json.dumps(dict(os.environ)))'
    import sys
    env = json.loads(subprocess.check_output([lake,'env',sys.executable,'-c',probe],cwd=root))
    lean = shutil.which('lean',path=env['PATH'])
    checker = shutil.which('leanchecker',path=env['PATH'])
    if not lean or not checker:
        raise RuntimeError('Missing compiler or kernel checker in the Lake environment.')
    cases = json.loads((folder/'traces.json').read_text(encoding='ascii'))
    orders = [case['q'] for case in cases]
    if orders != [q for q in eligible() if q < 169]:
        raise ValueError('The input must contain exactly the 18 eligible fields below 169.')
    if args.q is not None:
        if args.q not in orders:
            parser.error('Selected field is outside the finite check.')
        cases = [case for case in cases if case['q']==args.q]
    if args.sources:
        args.sources = args.sources.resolve()
        args.sources.mkdir(parents=True,exist_ok=True)
    stored = folder/'certificates'
    with TemporaryDirectory(prefix='lean-paley-traces-') as t:
        tmp = Path(t)
        env['LEAN_PATH'] = os.pathsep.join([str(tmp),env['LEAN_PATH']])
        def verify_case(case):
            check(case,root,tmp,lean,checker,env)
            src = tmp/f"PaleyBits{case['q']}.lean"
            if stored.is_dir() and args.sources != stored:
                if (stored/src.name).read_text(encoding='utf8') != src.read_text(encoding='utf8'):
                    raise ValueError(f'Generated theorem differs from the distributed source: {src.name}')
            if args.sources:
                shutil.copyfile(src,args.sources/src.name)
        with ThreadPoolExecutor(max_workers=min(args.jobs,len(cases))) as pool:
            for _ in pool.map(verify_case,cases):
                pass
    print(f"Kernel-checked {6*len(cases)} determinant bounds and {6*len(cases)} cube traces over {len(cases)} fields.",flush=True)


if __name__=='__main__':
    main()
