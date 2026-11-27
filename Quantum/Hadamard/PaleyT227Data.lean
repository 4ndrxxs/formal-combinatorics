import Quantum.Hadamard.GoethalsBits

/-! Exact Hamming counts for all pairs of four circulant block rows of size 227. -/
namespace Hadamard.PeriodicT.Block227
open HadamardMod
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def words : Fin 4 → Fin 4 → ℕ :=
  ![![43727896635352047844436095622873948551787259124413180809051433218150,4093547649666833128273725037637111788768764818049211907069901765944,91456254729535281352990804958087323979807009113867117325969042641073,206767612394784178470759484869186701964634464036794994006858371819694],
    ![167243266601519128864343286205848353061042997057458773859681213893055,171951676701853070512900025073283096837309896255911399039777448775576,7314335052865519552858410035277027379417176455634535034680197119125,88306156772058289358934625936078331357613625078281356801294229429011],
    ![193717010015006397516797659791692032003724172819540700242189006183826,146176396516940160344219894929263101195388187767702412754601438418398,43727896635352047844436095622873948551787259124413180809051433218150,156773600669317997977583772454336493293885407638728160652339862197282],
    ![18379148354491507334133000432707830752252491199980541260937425818273,92913875375742653706999931087404268093535883680796363452594983397842,100821301222364244858545786706730791794124832480041847246576959991621,171951676701853070512900025073283096837309896255911399039777448775576]]

theorem words_bound : ∀ i c, words i c < 2^227 := by decide +kernel

def ham (a b v : ℕ) := lowOnes 227 (a ^^^ cycleWord 227 b v)

def amount (i k : Fin 4) (v : ℕ) : ℕ :=
  ham (words i 0) (words k 0) v + ham (words i 1) (words k 1) v +
  ham (words i 2) (words k 2) v + ham (words i 3) (words k 3) v

private def allShifts (i k : Fin 4) : ℕ → Bool
  | 0 => true
  | v+1 => allShifts i k v && (amount i k v == if i=k ∧ v=0 then 0 else 454)

private theorem allShifts_ok (i k : Fin 4) (n : ℕ) (h : allShifts i k n = true)
    (v : ℕ) (hv : v<n) : amount i k v = if i=k ∧ v=0 then 0 else 454 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [allShifts, Bool.and_eq_true, beq_iff_eq] at h
    by_cases e : v=n
    · simpa [e] using h.2
    · exact ih h.1 (by omega)

private theorem shifts0 : allShifts 0 0 227 = true := by decide +kernel
private theorem shifts1 : allShifts 0 1 227 = true := by decide +kernel
private theorem shifts2 : allShifts 0 2 227 = true := by decide +kernel
private theorem shifts3 : allShifts 0 3 227 = true := by decide +kernel
private theorem shifts4 : allShifts 1 0 227 = true := by decide +kernel
private theorem shifts5 : allShifts 1 1 227 = true := by decide +kernel
private theorem shifts6 : allShifts 1 2 227 = true := by decide +kernel
private theorem shifts7 : allShifts 1 3 227 = true := by decide +kernel
private theorem shifts8 : allShifts 2 0 227 = true := by decide +kernel
private theorem shifts9 : allShifts 2 1 227 = true := by decide +kernel
private theorem shifts10 : allShifts 2 2 227 = true := by decide +kernel
private theorem shifts11 : allShifts 2 3 227 = true := by decide +kernel
private theorem shifts12 : allShifts 3 0 227 = true := by decide +kernel
private theorem shifts13 : allShifts 3 1 227 = true := by decide +kernel
private theorem shifts14 : allShifts 3 2 227 = true := by decide +kernel
private theorem shifts15 : allShifts 3 3 227 = true := by decide +kernel

theorem totals (i k : Fin 4) (v : Fin 227) :
    amount i k v.val = if i=k ∧ v.val=0 then 0 else 454 := by
  apply allShifts_ok i k 227 _ v.val v.isLt
  fin_cases i <;> fin_cases k
  · exact shifts0
  · exact shifts1
  · exact shifts2
  · exact shifts3
  · exact shifts4
  · exact shifts5
  · exact shifts6
  · exact shifts7
  · exact shifts8
  · exact shifts9
  · exact shifts10
  · exact shifts11
  · exact shifts12
  · exact shifts13
  · exact shifts14
  · exact shifts15

end Hadamard.PeriodicT.Block227

