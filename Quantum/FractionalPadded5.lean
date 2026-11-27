module
public import Quantum.FractionalPhysicalCut

/-! A direct physical parity counterexample at block side 5, with four active
quantum rays and 21 distinct printed exterior symbols in every context. -/
@[expose] public section
namespace ImpossiblePadded5
open QuantumSudoku FractionalLayouts PhysicalSudokuCut PartialSudoku ImpossibleSudoku
abbrev F := Fin 5
abbrev P := Sites 5
abbrev U := Fin 21

def codes : ℕ → Packed
  | 0 => ⟨6,0x1c7660608e7a9ba29ada91f019898845784b25⟩
  | 1 => ⟨6,0x2a92161b72b9475626603908dea6c7e77666a8⟩
  | 2 => ⟨6,0x2969fae539942282755eb2171d987a1b92a623⟩
  | 3 => ⟨6,0x220c0668b1e6987e57667236e4a829e9ae0061⟩
  | 4 => ⟨6,0x277828eca6499d85b1ea6286ab80896265c01f⟩
  | 5 => ⟨6,0x1da1c9a2aea6009418197e91639216de6ac127⟩
  | 6 => ⟨6,0x2ba983646607e8b0278c86205a9e5a5d9a371b⟩
  | 7 => ⟨6,0x1b0a07e99081e18ab8ec6a77667007a5a98a19⟩
  | 8 => ⟨6,0xc05ab216c27a78dd99c94d66a6288ab8247e9⟩
  | 9 => ⟨6,0x1e6639676a6729764a98a1bae0b1f10a517862⟩
  | 10 => ⟨6,0x2695d0991c0a249e071b8eb798862a9ab1fa48⟩
  | 11 => ⟨6,0x246226c8a9d82b661391a5e7ec9676a67288d4⟩
  | 12 => ⟨6,0x207c7a2b798848a5ab2589998b8dc76a3a76e4⟩
  | 13 => ⟨6,0x2102aa5c8ac8c26a69df21d907a1b66061e96b⟩
  | 14 => ⟨6,0x1a8ec9de7dc6e59aa6285248174a9ad946189d⟩
  | 15 => ⟨6,0x119887a36283aa91c7e9ae08a175952c95b9da⟩
  | 16 => ⟨6,0x1881b92a55fa6cae88626569e569e29c8dd166⟩
  | 17 => ⟨6,0x1fae97548218996ec96779a11c5e3998a0a92a⟩
  | 18 => ⟨6,0x1986870e95a9de1d8423766aa96e4b157e2ae0⟩
  | 19 => ⟨6,0x2c9e589a9a375c40d9066ea6287eb81686965e⟩
  | 20 => ⟨6,0x2371e32685b92061fa6b44696265d5e89daaac⟩
  | 21 => ⟨6,0x286e4a91769adf3998a1825b2779a62321499c⟩
  | 22 => ⟨6,0x6a6b81da22663a8c6979ec85f4667246e5798⟩
  | 23 => ⟨6,0x178998589e5b1a7a36dd99ca1252a91fa6b811⟩
  | 24 => ⟨6,0x25b2769f40756671ea24a98a5bae08e189974e⟩
  | _ => ⟨1,0⟩

def placements : ℕ → Packed
  | 0 => ⟨5,0x16c5cf9580b99cb450ef88310620aa9⟩
  | 1 => ⟨5,0x6960e020a374bacc2a073a05b57a970⟩
  | 2 => ⟨5,0xba8b0571e830414fb310925e416c666⟩
  | 3 => ⟨5,0x1319c942b1c8560027c9ab4c6b0b9836⟩
  | 4 => ⟨5,0x144326ac44b2a91e705e027246b336c1⟩
  | 5 => ⟨5,0x29c957055e7450cd5931628d91485d0⟩
  | 6 => ⟨5,0xfc5cb038cd4129728b48102276ab1c9⟩
  | 7 => ⟨5,0xc70e81520936be16a9527c2c02946e6⟩
  | 8 => ⟨5,0x152200683562796830c5cc9d92756257⟩
  | 9 => ⟨5,0x74b60ba4aaeb0028361f154eec10c85⟩
  | 10 => ⟨5,0x3514317e2f0598ee126cd6128804eb2⟩
  | 11 => ⟨5,0x884d62310f80d9d14aa43a95f7031b4⟩
  | 12 => ⟨5,0xda11f5125803ae38bcca60b9521a216⟩
  | 13 => ⟨5,0x1205aa76b8298cf046095433ca35a217⟩
  | 14 => ⟨5,0x162b8ccabe0ab84499d0128e08d42ce3⟩
  | 15 => ⟨5,0x45c1920dc6fa250a6d4ee100d32e236⟩
  | 16 => ⟨5,0x107d22e481151b1b791844b1d7854ca1⟩
  | 17 => ⟨5,0xeb82c3615a134653c2ea87aa043d049⟩
  | 18 => ⟨5,0x50a5168aa6660ae01c1753cb0e2368f⟩
  | 19 => ⟨5,0x1832848bcecd95465382305d02923dcc⟩
  | 20 => ⟨5,0x605a41d131c2270758d7908ef2aeaa⟩
  | 21 => ⟨5,0x98d658405562358b81e60b99c5151e3⟩
  | 22 => ⟨5,0xab3ef35984484935406851b62061dd8⟩
  | 23 => ⟨5,0x11118699ae4575ea123d8a6c2d4c1d00⟩
  | 24 => ⟨5,0x173ad2db430c28c86a382f4544a8cc12⟩
  | 25 => ⟨5,0x146c5012c00c1247224dd533cf65df0a⟩
  | 26 => ⟨5,0x951477d5b15b93745b066066281464⟩
  | 27 => ⟨5,0x5b8a6b606c8349c3536047d3074d620⟩
  | 28 => ⟨5,0xa19ef1a19e2862689002bb148d4b995⟩
  | 29 => ⟨5,0xf430740acf6a930db94d0129d19c920⟩
  | 30 => ⟨5,0x12728c21c497c201309d962adb5a3e09⟩
  | 31 => ⟨5,0x19ddc85d8d28a8b84c28c6d5e020867⟩
  | 32 => ⟨5,0x9c0c2d30965601449d5e7942888ddd6⟩
  | 33 => ⟨5,0xb22253a9e032d1e9b0451c180a75d8d⟩
  | 34 => ⟨5,0x154cb178328d0bece5a8e2191132c4c0⟩
  | 35 => ⟨5,0x1654ca43caae1984f02db74c59880514⟩
  | 36 => ⟨5,0x27e169b5d00530d52c64399e047502d⟩
  | 37 => ⟨5,0x7a11ee88d98942a168ae8500a9b2cd3⟩
  | 38 => ⟨5,0xc026986a2333d6057986abd82e14964⟩
  | 39 => ⟨5,0x113b81013469b856aa610f232b29d8c5⟩
  | 40 => ⟨5,0x685980538af41c821dd388b5740ceb2⟩
  | 41 => ⟨5,0x105bd26461cab08f4ac89305e23605a5⟩
  | 42 => ⟨5,0x17a820a910346c58b3226970ec5c09e7⟩
  | 43 => ⟨5,0xd096af026e49da2680d6ea484c3e10a⟩
  | 44 => ⟨5,0x32ac96bce4703691732a1424cf8604a⟩
  | 45 => ⟨5,0x4640e34d04679500c3acd0cd578d64b⟩
  | 46 => ⟨5,0x8155ac7153024ef63be325e06135140⟩
  | 47 => ⟨5,0xeb3632c02754ac2715145822e67b083⟩
  | 48 => ⟨5,0x1889ac59bd4175e5061014a892b19d0d⟩
  | 49 => ⟨5,0x133045522b0ba0dac8a4a03ba50bbd16⟩
  | 50 => ⟨5,0x19326549c0d561f1a0d1671aeb20a15⟩
  | 51 => ⟨5,0x6bc4ea7b292488162a1ae9e061aae04⟩
  | 52 => ⟨5,0xb1d894746617a54703250c0915694d7⟩
  | 53 => ⟨5,0x1340b001d8f722e8a7caa90c5b02b1c6⟩
  | 54 => ⟨5,0x145a5cfc0948acce065c642b60695831⟩
  | 55 => ⟨5,0x29b5eb021d13d2b28112628d4cb5f01⟩
  | 56 => ⟨5,0x16c48b03b4c21bc37aa9cc022712512b⟩
  | 57 => ⟨5,0xc75c1554a18694c30a271a2c5679d24⟩
  | 58 => ⟨5,0x520ea685c0e7a9683c6969e1226b241⟩
  | 59 => ⟨5,0x104a143a06a5b01ec5e082746e734db2⟩
  | 60 => ⟨5,0x37b8276260a356d314688593122dda0⟩
  | 61 => ⟨5,0x8a02b1338f3604584914b815e3bd9b2⟩
  | 62 => ⟨5,0xd060d694d940ad24895e313957a9d10⟩
  | 63 => ⟨5,0x1232542052a18cd87c3917b3cad59203⟩
  | 64 => ⟨5,0x165460ba9069b9e6e6d04f360082b032⟩
  | 65 => ⟨5,0x482acd0946b446ef950e9102aec4d86⟩
  | 66 => ⟨5,0xface574a91059074b184d89c38600ae⟩
  | 67 => ⟨5,0xe0d04963db789d001ae04aa8d32cb16⟩
  | 68 => ⟨5,0x6284e38e260bb1ae442d5549644d04f⟩
  | 69 => ⟨5,0x1869591b8ec605648705703d269511e2⟩
  | 70 => ⟨5,0x886441998e4df109aea568aca3be88⟩
  | 71 => ⟨5,0x9b431342c8fa0dd569c2ab98450464c⟩
  | 72 => ⟨5,0xa154775c0b69a0e62622f93534605c0⟩
  | 73 => ⟨5,0x113a90e9d6425b48133d341c180b60b7⟩
  | 74 => ⟨5,0x17619a9b030724a0ba09434562f9942e⟩
  | _ => ⟨1,0⟩

def frames : ℕ → Packed
  | 0 => ⟨3,0xb08⟩
  | 1 => ⟨5,0xac1c7⟩
  | 2 => ⟨5,0xac1c7⟩
  | 3 => ⟨2,0xe4⟩
  | 4 => ⟨4,0x8720⟩
  | 5 => ⟨3,0xb08⟩
  | 6 => ⟨4,0xdc21⟩
  | 7 => ⟨4,0x8720⟩
  | 8 => ⟨4,0xdc21⟩
  | 9 => ⟨5,0xbd144⟩
  | 10 => ⟨4,0x8720⟩
  | 11 => ⟨5,0xa45c8⟩
  | 12 => ⟨4,0xeb87⟩
  | 13 => ⟨4,0x8720⟩
  | 14 => ⟨5,0xbd251⟩
  | 15 => ⟨5,0xa45c8⟩
  | 16 => ⟨5,0xb5545⟩
  | 17 => ⟨5,0xbd144⟩
  | 18 => ⟨5,0xac1c7⟩
  | 19 => ⟨5,0xb41a6⟩
  | 20 => ⟨5,0xbc586⟩
  | 21 => ⟨5,0xa45c8⟩
  | 22 => ⟨5,0xbc586⟩
  | 23 => ⟨5,0xbd251⟩
  | 24 => ⟨5,0xac1c7⟩
  | 25 => ⟨5,0xa45c8⟩
  | 26 => ⟨3,0xb08⟩
  | 27 => ⟨5,0xbd144⟩
  | 28 => ⟨5,0xa45c8⟩
  | 29 => ⟨5,0xb5545⟩
  | 30 => ⟨5,0xbd144⟩
  | 31 => ⟨4,0x8720⟩
  | 32 => ⟨5,0xbd251⟩
  | 33 => ⟨5,0xbc967⟩
  | 34 => ⟨3,0xb08⟩
  | 35 => ⟨5,0xb41a6⟩
  | 36 => ⟨5,0xa45c8⟩
  | 37 => ⟨5,0xbc586⟩
  | 38 => ⟨5,0xac1c7⟩
  | 39 => ⟨4,0xdc21⟩
  | 40 => ⟨5,0xac1c7⟩
  | 41 => ⟨4,0x8720⟩
  | 42 => ⟨5,0xac1c7⟩
  | 43 => ⟨4,0x8720⟩
  | 44 => ⟨5,0xac1c7⟩
  | 45 => ⟨5,0xa45c8⟩
  | 46 => ⟨4,0xdc21⟩
  | 47 => ⟨4,0x8720⟩
  | 48 => ⟨2,0xe4⟩
  | 49 => ⟨5,0xbc586⟩
  | 50 => ⟨3,0xb08⟩
  | 51 => ⟨4,0x8720⟩
  | 52 => ⟨5,0xac1c7⟩
  | 53 => ⟨5,0xac1c7⟩
  | 54 => ⟨2,0xe4⟩
  | 55 => ⟨5,0xbd144⟩
  | 56 => ⟨3,0xb08⟩
  | 57 => ⟨4,0xdc21⟩
  | 58 => ⟨4,0x8720⟩
  | 59 => ⟨4,0xdc21⟩
  | 60 => ⟨5,0xa45c8⟩
  | 61 => ⟨5,0xbc967⟩
  | 62 => ⟨5,0xa45c8⟩
  | 63 => ⟨4,0x8720⟩
  | 64 => ⟨4,0x8720⟩
  | 65 => ⟨5,0xb5545⟩
  | 66 => ⟨5,0xbd144⟩
  | 67 => ⟨5,0xb41a6⟩
  | 68 => ⟨5,0xac1c7⟩
  | 69 => ⟨5,0xa45c8⟩
  | 70 => ⟨5,0xa45c8⟩
  | 71 => ⟨5,0xbd251⟩
  | 72 => ⟨5,0xbc586⟩
  | 73 => ⟨5,0xac1c7⟩
  | 74 => ⟨5,0xbc586⟩
  | _ => ⟨1,0⟩

def selected : ℕ → Packed
  | 0 => ⟨1,0x318c63⟩
  | 1 => ⟨1,0x318c63⟩
  | 2 => ⟨1,0x1c30c3⟩
  | _ => ⟨1,0⟩

def index (p : P) : ℕ := p.1.val*5+p.2.val
def decode (q : ℕ) : PartialSudoku.Code 21 :=
  if h:q<24 then .inl ⟨q,h⟩ else .inr (Fin.ofNat 21 (q-24))
def label (r c : P) : PartialSudoku.Code 21 := decode ((codes (index r))[index c]!)
def frame (d : Direction) (k : P) (i : Fin 4) :=
  Fin.ofNat 24 ((frames (axis d*25+index k))[i.val]!)
def place (d : Direction) (k : P) (s : PartialSudoku.Word 21) : P :=
  let i := Sum.elim (fun h => h.val) (fun u => 4+u.val) s
  let pos := (placements (axis d*25+index k))[i]!
  (Fin.ofNat 5 (pos/5),Fin.ofNat 5 (pos%5))
def mark (d : Direction) (k : P) : ZMod 2 := (selected (axis d))[index k]!

set_option maxRecDepth 120000
set_option maxHeartbeats 0
def model : PhysicalSudokuCut.Full 5 21 where
  dims := by decide
  label := label
  place := place
  frame := frame
  checked := by intro d; cases d <;> decide +kernel
  ortho := by intro d; cases d <;> decide +kernel

def parity : PhysicalSudokuCut.Cut model where
  mark := mark
  active := by decide +kernel
  odd := by decide +kernel

theorem counterexample : ∃ (p : P→P→Option P) (v : Grid F),
    QuantumCompletes p v ∧ ¬∃ f, ClassicalCompletes p f :=
  PhysicalSudokuCut.counterexample model parity

#print axioms counterexample
end ImpossiblePadded5
