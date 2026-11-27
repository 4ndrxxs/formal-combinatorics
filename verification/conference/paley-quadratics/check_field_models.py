"""Generate and replay the field interpretation of the eleven required small certificates."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

from check_lean_traces import lake_project
from check_projective import eligible
from check_trace import Field


MODULE = "Quantum.Hadamard.ProjectiveFieldModels"
FOLDER = Path(__file__).resolve().parent
SMALL = [q for q in eligible() if q < 109]
PATTERNS = {
    "SplitSquares": ".split true true",
    "SplitNonsquares": ".split false true",
    "SplitSquaresOpposite": ".split false false",
    "SplitNonsquaresOpposite": ".split true false",
    "NonsplitNegative": ".nonsplit false",
    "NonsplitNegativeOpposite": ".nonsplit true",
}


def packed(values):
    return sum(value << (8 * i) for i, value in enumerate(values))


def extension_source(field):
    q = field.q
    plus = [packed(field.add(i, j) for j in range(q)) for i in range(q)]
    times = [packed(field.mul(i, j) for j in range(q)) for i in range(q)]
    neg = packed(field.sub(0, i) for i in range(q))
    inv = packed(field.inv(i) if i else 0 for i in range(q))
    rows = "\n".join(f"private theorem law{i} : rowLaw {i} := by decide +kernel"
                     for i in range(q))
    combine = "\n".join(f"  have h := extend_check h law{i}" for i in range(q))
    return f"""
structure Element where
  rep : Fin {q}
  deriving DecidableEq, Fintype, Inhabited

def numbers : Fin {q} ≃ Element := ⟨Element.mk,Element.rep,fun _ ↦ rfl,fun _ ↦ rfl⟩

private def plusRows : Array ℕ := #[{", ".join(map(str, plus))}]
private def timesRows : Array ℕ := #[{", ".join(map(str, times))}]

private def byte (w : ℕ) (i : Fin {q}) : Element :=
  ⟨Fin.ofNat {q} ((w >>> (8*i.val))%256)⟩

local instance : Zero Element := ⟨⟨0⟩⟩
local instance : One Element := ⟨⟨1⟩⟩
local instance : Add Element := ⟨fun i j ↦ byte (plusRows[i.rep.val]!) j.rep⟩
local instance : Mul Element := ⟨fun i j ↦ byte (timesRows[i.rep.val]!) j.rep⟩
local instance : Neg Element := ⟨fun i ↦ byte {neg} i.rep⟩
local instance : Inv Element := ⟨fun i ↦ byte {inv} i.rep⟩

private def rowLaw (i : ℕ) : Prop := ∀ j k : Fin {q},
  let a := numbers (Fin.ofNat {q} i)
  let b := numbers j
  let c := numbers k
  a+b+c=a+(b+c) ∧ a*b*c=a*(b*c) ∧ a*(b+c)=a*b+a*c

private instance (i : ℕ) : Decidable (rowLaw i) := by unfold rowLaw; infer_instance

{rows}

private theorem laws (a b c : Element) :
    a+b+c=a+(b+c) ∧ a*b*c=a*(b*c) ∧ a*(b+c)=a*b+a*c := by
  have h : ∀ i<0,rowLaw i := by intro i hi; omega
{combine}
  have atIndex := h a.rep.val a.rep.isLt b.rep c.rep
  have fix : Fin.ofNat {q} a.rep.val=a.rep := Fin.ext (Nat.mod_eq_of_lt a.rep.isLt)
  dsimp only at atIndex
  rw [fix] at atIndex
  exact atIndex

instance : Field Element := Field.ofMinimalAxioms Element
  (fun a b c ↦ (laws a b c).1) (by decide +kernel) (by decide +kernel)
  (fun a b c ↦ (laws a b c).2.1) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (fun a b c ↦ (laws a b c).2.2)
  ⟨numbers 0,numbers 1,by decide +kernel⟩

private def encode (u : Element) : ℕ := u.rep.val
"""


def model_source(q):
    field = Field(q)
    n, v = q + 1, (q + 1) // 2
    base = f"PaleyBits{q}"
    if q == field.p:
        model = f"""
instance : Fact (Nat.Prime {q}) := ⟨by decide⟩
abbrev Element := ZMod {q}
def numbers : Fin {q} ≃ Element := Equiv.refl _
private def encode (u : Element) : ℕ := u.val
"""
    else:
        model = extension_source(field)
    positive = sum(1 << u for u in range(q) if field.char[u] == 1)
    sections = [f"""import {MODULE}
import {base}

open Hadamard.ProjectiveSigning Hadamard.BitTrace
set_option maxHeartbeats 40000000
set_option maxRecDepth 200000
namespace PaleyField{q}
""", model, f"""
private def readChar (u : Element) : ℤ :=
  if encode u=0 then 0 else if ({positive}:ℕ).testBit (encode u) then 1 else -1

private theorem character : ∀u, readChar u=quadraticChar Element u :=
  character_by_squares readChar (by decide +kernel) (by decide +kernel) (by decide +kernel)

def nonsquare : Element := numbers {field.d}
private theorem negative : quadraticChar Element nonsquare= -1 := by
  rw [←character]; decide +kernel

private theorem entries : ∀i j : Fin {n}, tableEntry readChar (chart numbers i) (chart numbers j)=
    sign ({base}.fullRows i) j.val - (if i=j then 1 else 0 : ℤ) := by decide +kernel

theorem card : Fintype.card Element={q} := (Fintype.card_congr numbers.symm).trans (Fintype.card_fin _)
"""]
    for label, pat in PATTERNS.items():
        sections.append(f"""
private theorem bound{label} :
    fourFifths {q} ≤ signedDet (({pat} : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin {v} ⊕ Fin {v},
      ({pat} : Pattern).read readChar nonsquare (chart numbers ({base}.{label}.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character {base}.fullRows entries
    nonsquare ({pat}) {base}.{label}.indexing diags]
  exact {base}.{label}.determinant_bound
""")
    sections.append(f"""
theorem canonical : CertifiedPatterns Element := by
  refine ⟨nonsquare,negative,?_⟩
  intro pat
  rw [card]
  cases pat with
  | split o z =>
    cases o <;> cases z
    · exact boundSplitSquaresOpposite
    · exact boundSplitNonsquares
    · exact boundSplitNonsquaresOpposite
    · exact boundSplitSquares
  | nonsplit o =>
    cases o
    · exact boundNonsplitNegative
    · exact boundNonsplitNegativeOpposite

#print axioms canonical
end PaleyField{q}
""")
    return "\n".join(sections)


def all_orders_source():
    imports = "\n".join(f"import PaleyField{q}" for q in SMALL)
    cases = " ∨ ".join(f"q.val={q}" for q in SMALL)
    branches = "\n".join(f"  · exact certified_of_card (h.trans PaleyField{q}.card.symm) PaleyField{q}.canonical"
                         for q in SMALL)
    alternatives = "|".join("h" for _ in SMALL)
    return f"""{imports}

noncomputable section
open Finset Matrix
namespace Hadamard.ProjectiveSigning

private theorem smallOrders : ∀q : Fin 109, 29≤q.val → q.val%4=1 → IsPrimePow q.val →
    {cases} := by decide +kernel

private theorem smallCertified (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (lo : 29≤Fintype.card F) (hi : Fintype.card F<109) (q4 : Fintype.card F%4=1) :
    CertifiedPatterns F := by
  have h := smallOrders ⟨Fintype.card F,hi⟩ lo q4 (FiniteField.isPrimePow_card F)
  obtain {alternatives} := h
{branches}

/-- The four-fifths bound for the actual real Paley matrix and every
nonsingular quadratic signing at every eligible order starting at 30. -/
theorem quadratic_paley_four_fifths_all {{F : Type}} [Field F] [Fintype F] [DecidableEq F]
    (q4 : Fintype.card F%4=1) (lo : 29≤Fintype.card F)
    (a b c : F) (disc : b^2-4*a*c≠0) (s : Option F→Bool) (w : ℤ) (unit : w^2=1)
    (agree : ∀i, quadraticValue a b c i≠0 →
      (if s i then (1:ℤ) else -1)=w*quadraticChar F (quadraticValue a b c i))
    (ties : (∑ i, if quadraticValue a b c i=0 then (if s i then (1:ℤ) else -1) else 0)=0) :
    let q := Fintype.card F
    (4/5:ℝ)*(2*(q:ℝ))*((q:ℝ)-1)^(q/2) ≤
      |(realPaley+diagonal (fun i ↦ if s i then (1:ℝ) else -1)).det| := by
  have hc : ringChar F≠2 := by
    intro h
    have := FiniteField.even_card_of_char_two h
    omega
  by_cases large : 109≤Fintype.card F
  · exact quadratic_paley_four_fifths_109 hc q4 large a b c disc s w agree ties
  have m := smallCertified F lo (by omega) q4
  have bound := quadratic_of_certified m hc q4 a b c disc s w unit agree ties
  simpa [fourFifths,signedDet,signOf,Int.cast_ite,mul_assoc] using bound

#print axioms quadratic_paley_four_fifths_all
end Hadamard.ProjectiveSigning
"""


def sources():
    return {**{f"PaleyField{q}": model_source(q) for q in SMALL},
            "PaleyAllOrders": all_orders_source()}


def verify(project, directory, jobs):
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin" / ("lake.exe" if os.name == "nt" else "lake"))
    subprocess.run([lake, "build", MODULE, "Quantum.Hadamard.ProjectiveSplitComparison"], cwd=project, check=True, stdout=subprocess.DEVNULL)
    command = [lake, "env", sys.executable, "-c", "import json,os;print(json.dumps(dict(os.environ)))"]
    env = json.loads(subprocess.check_output(command, cwd=project, text=True))
    with TemporaryDirectory(prefix="lean-field-models-") as temporary:
        tmp = Path(temporary)
        env["LEAN_PATH"] = str(tmp) + os.pathsep + env["LEAN_PATH"]

        def build(name):
            source = directory / (name + ".lean")
            result = subprocess.run(["lean", "-R", str(directory), "-o", str(tmp / (name + ".olean")), str(source)],
                                    cwd=project, env=env, capture_output=True, text=True, encoding="utf8")
            if result.returncode or "sorryAx" in result.stdout:
                raise RuntimeError(name + "\n" + result.stdout + result.stderr)
            reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", " ".join(result.stdout.split()))
            if name.startswith("PaleyBits"):
                expected = {f"{name}.{label}.{theorem}" for label in PATTERNS
                            for theorem in ("certificate", "determinant_bound")}
            elif name.startswith("PaleyField"):
                expected = {name + ".canonical"}
            elif name == "PaleyAllOrders":
                expected = {"Hadamard.ProjectiveSigning.quadratic_paley_four_fifths_all"}
            elif name == "PaleyRawStatement":
                expected = {"PaleyQuadraticStatement.verified"}
            elif name == "PaleySourceBorders":
                expected = {"Hadamard.MSXCore.source_borders_four_fifths"}
            else:
                raise ValueError("Unrecognized certificate module " + name)
            allowed = {"propext", "Classical.choice", "Quot.sound"}
            if {theorem for theorem, _ in reports} != expected or any(
                    set(axioms.split(", ")) - allowed for _, axioms in reports):
                raise RuntimeError("Missing or unexpected axiom report for " + name)
            subprocess.run(["leanchecker", "-v", name], cwd=tmp, env=env, check=True)
            print("Verified", name, flush=True)

        def field(q):
            build(f"PaleyBits{q}")
            build(f"PaleyField{q}")

        with ThreadPoolExecutor(max_workers=jobs) as pool:
            list(pool.map(field, SMALL))
        build("PaleyAllOrders")
        build("PaleyRawStatement")
        build("PaleySourceBorders")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Regenerate the committed finite-field sources.")
    parser.add_argument("--project", type=Path, default=lake_project(FOLDER))
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    directory = FOLDER / "certificates"
    for name, data in sources().items():
        path = directory / (name + ".lean")
        if args.write:
            path.write_text(data, encoding="utf8", newline="\n")
        elif path.read_text(encoding="utf8") != data:
            raise ValueError("Generated and distributed Lean sources differ at " + path.name)
    if args.write:
        print(f"Wrote {len(SMALL)} field models and the all-order theorem.")
        return
    if args.project is None or args.jobs < 1:
        parser.error("Pass a Lake project and a positive job count.")
    verify(args.project.resolve(), directory, args.jobs)


if __name__ == "__main__":
    main()
