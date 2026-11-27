module
public import Quantum.FractionalPartialCut

/-! A classically impossible partial Sudoku of block side 7, with an
actual rank-one quantum completion and a direct parity certificate. -/
@[expose] public section
namespace ImpossibleSudoku7
open QuantumSudoku FractionalLayouts PartialSudoku ImpossibleSudoku

def codes : Packed := ⟨7,0x6011a6030cbc7c059af5cd56a970b15aa6511ca84e992c1488612344c603f3ed9d0d86dd01b3cede9d38d1a1b3c05a9d38dcc4434e9c195af61bf5eb99c2530162b5411200509d32564c50bc4689db0407c2be82e5b33407dc3f74f4e03367a1433a65e1872698bb6cb453488bd7307ca412c56a992482a13a64ad5ba1808d10f7701b217c8d10b6480fbc68c4e9c6e6cf4226fccb530c0d385d056c37a217aa88594b958ad2b348e94274c992b148c942744c1cbb42391c0745501f6d0619d38ccd9e6e1da196a6221a5eb9ead70f882b54fe12978b162b5505ba9729d3256c91ea8468980c6885a9762f99203ee9e3b3a7199b3c69fc23218c4070bd7445a461c486bd70d5b0a0ac56aa03f52a13a64a2523e7a8d13c76510ba72e1bb6407cf356874e333648d326265818⟩

def positions : Packed := ⟨6,0x646615262f0c96c2b47a1f72989d91e3d79cd396b843145652d3b23ac1661a88830690280586b176c87a7809482b9cac141568a4c73df14d3a6b443147432e48a3a91669018a30be58689c876638a3e4aab4c265b601bc050b1875ee14d7a5b44315b0371a8a92518704208df5921d738d7278ea0d35608823107d1280c2f18f9ae156765b44524b1b49a841259a0862ba5e2dfae18c589b5da0e858f342a4b254b189ef1de9ae395765b4c7244ca499a81460010c0818442166db053cc3a48a3a2b4af681ba001f9c659e98d51576511b70b08a469a896302174c70ee1c6488b048b080a3584632ea9e56a45dfbce59e14c51576d4db0eb089869050a0099c64f18500a69e5dca9b7477c9665a62412b440c134c2c83ce5134565588609e48e8babc2fb260a775e1820702174654a4a4aad6b9a553b6ca8510300734c2c939441961f7228268e8be16cfaa758e52602885c4dfbd93c7263add2e5929badb3018510304d3084505db6987a281548a09e529ae76cb183087c153a265f44a31775c866964a2fbadb2a14400920f4d24166988e03413d8bdaaea85734c1851030914c98ec8956d979d7209e6964a6eb700401cb2883924287d651ab0b80730f4a792e5d0aef144062a6351345655b61f79d7219a5a2ac060c200d288b593892874657d29ad3ee6243618e2a9a10304c2c93944d05d655b65e760a68becaf014202770819c25358f3a90ea10b6e120c9009dd42d9a58e07de89a6585d54915073450811aeaf0beca0a9e06c265f0e12c894192902cc1c38d1de76261759a49140f50a24c185babaaf9a3a2d5531179252c3b13aa172b7ed15b198c0d7545956903ce48a2481cc08112fba68e99de8a0a19440311753bdbb109700c9560b99905a235ce51220734a08100612baad9e67a285f59a62970f2cf6c37221082c19a19c955d45362cba834c2801850abab0bed8e995f7966995ce4909205070c02ed1cc66451356a1ac99c79061a805102c2fbab8e9a2796285d5d639244f34a21f6c9070beaa6591c6d85d44d245030b2040c1badae89e68e28607dd69954f38d2891c5080b1e586⟩

def frames : Packed := ⟨5,0x59ef2104032aad56844c619a943a3423e701302d08d6e9d58922af4009076da062be321302d090051a84f5cd16754f065cd16a692⟩

def selected : Packed := ⟨1,0x68726⟩

abbrev F := Fin 7
abbrev U := Fin 45
def decode (q : ℕ) : PartialSudoku.Code 45 :=
  if h : q<24 then .inl ⟨q,h⟩ else .inr (Fin.ofNat 45 (q-24))
def label (r c t : F) : PartialSudoku.Code 45 := decode (codes[(r.val*7+c.val)*7+t.val]!)
def frame (d : Direction) (k : F) (h : Fin 4) : Fin 24 :=
  Fin.ofNat 24 (frames[(axis d*7+k.val)*4+h.val]!)
def place (d : Direction) (k : F) (s : PartialSudoku.Word 45) : Sites 7 :=
  let i := Sum.elim (fun h => h.val) (fun u => 4+u.val) s
  let w := positions[(axis d*7+k.val)*49+i]!
  (Fin.ofNat 7 (w/7),Fin.ofNat 7 (w%7))

set_option maxRecDepth 100000
set_option maxHeartbeats 0
def model : PartialSudoku.Layout 7 45 where
  dims := by decide
  label := label
  place := place
  frame := frame
  checked := by intro d; cases d <;> decide +kernel
  ortho := by intro d; cases d <;> decide +kernel

def mark (d : ℕ) (k : F) : ZMod 2 := selected[d*7+k.val]!

def proofCut : PartialSudoku.Cut model where
  row := mark 0
  col := mark 1
  block := mark 2
  on_active := by
    have cert : ∀ r c t : F,(model.label r c t).isLeft=true →
        mark 0 r+mark 1 c+mark 2 t=0 := by decide +kernel
    intro r c t
    cases h : model.label r c t with
    | inl v => exact cert r c t (by simp [h])
    | inr u => trivial
  odd := by decide +kernel

theorem quantum_completion : PartialSudoku.QuantumCompletes model.puzzle model.board := model.quantum
theorem no_classical_completion : ¬∃ f,PartialSudoku.ClassicalCompletes model.puzzle f := proofCut.impossible model
theorem counterexample :
    ∃ (p : Sites 7→Sites 7→Option (Sites 7)) (v : Grid F),
      PartialSudoku.QuantumCompletes p v ∧ ¬∃ f,PartialSudoku.ClassicalCompletes p f :=
  PartialSudoku.cut_counterexample model proofCut

#print axioms quantum_completion
#print axioms no_classical_completion
#print axioms counterexample
end ImpossibleSudoku7
