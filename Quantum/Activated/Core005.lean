module
public import Quantum.Activated.Constraints
public import Quantum.FractionalImpossibleTables

@[expose] public section
namespace Activated.Core005
open ImpossibleSudoku
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bases : ℕ → Packed
  | 0 => ⟨3,0xc147e958d8f83e889e7c2374b3e21ad2a67807455feb46297c686a668eb49716b8163c8f7d414e3c3d2a446be3ba7650062d5f4cfb30ed098de0ab1ecab3e06255b99c2c5dec8574377813⟩
  | _ => ⟨1,0⟩

def pins : ℕ → Packed
  | 0 => ⟨1,0x86526844a0e225b25a2be2c9554ebef07d9fa1ede5ffc987fc⟩
  | _ => ⟨1,0⟩

def lines : ℕ → Packed
  | 0 => ⟨5,0xc6318c6318bdef7bdef7b5ad6b5ad6ad6b5ad6b5a5294a52949ce739ce7394a5294a528c6318c63184210842107bdef7bdef739ce739ce6b5ad6b5ad6318c6318c5ad6b5ad6b5294a5294a4a5294a529421084210839ce739ce7318c6318c6294a5294a5210842108418c6318c63108421084208421084210000000000⟩
  | 1 => ⟨5,0xb567289ca0c4e0e41c40c5a0e6b167a45e831062c558b51462bd24f730c4a4a2f6b081bd18a49cc29bd4939461c5a9159420c5eab41ca3bc60f6ad00b520e41c62a41ac31420ace4f5a880b526929062c5ed283d44bca2e6ad46c55cc4a0e29c1c940c20c5aad4a0c1bda2a31461bd671734c0941eb52481ace4d62482⟩
  | 2 => ⟨5,0xc62f7bd6b4c5ef6ad694c62f6b5ad5c5ef5ad294c62d6b56949ce528c60f9ca528c5ef9ce318420f94a30841ef9ce728c1ef739cc5ad6a735ad6316a739ac5ad4a7358c5ad4a735ad6314a4a506314a54a528420e54a10739ce64a4e7318c5420e6314a521082084202106208400210631082018c621040020c6210400⟩
  | _ => ⟨1,0⟩

def groups : ℕ → Packed
  | 0 => ⟨3,0xfac688⟩
  | 1 => ⟨4,0xfedcba98⟩
  | 2 => ⟨5,0xbdab49ca30⟩
  | 3 => ⟨5,0xffbbcdeb38⟩
  | 4 => ⟨6,0x9e69648e2860⟩
  | 5 => ⟨6,0xbeeb6caeaa68⟩
  | 6 => ⟨6,0xdf6d74cf2c70⟩
  | 7 => ⟨6,0xffef7cefae78⟩
  | 8 => ⟨7,0x8f1a2c4870a0c0⟩
  | 9 => ⟨7,0x9f3a6cc972a4c8⟩
  | 10 => ⟨7,0xaf5aad4a74a8d0⟩
  | 11 => ⟨7,0xbf7aedcb76acd8⟩
  | 12 => ⟨7,0xcf9b2e4c78b0e0⟩
  | 13 => ⟨7,0xdfbb6ecd7ab4e8⟩
  | 14 => ⟨7,0xefdbaf4e7cb8f0⟩
  | 15 => ⟨7,0xfffbefcf7ebcf8⟩
  | 16 => ⟨8,0x8786858483828180⟩
  | 17 => ⟨8,0x8f8e8d8c8b8a8988⟩
  | 18 => ⟨8,0x9796959493929190⟩
  | 19 => ⟨8,0x9f9e9d9c9b9a9998⟩
  | 20 => ⟨8,0xa7a6a5a4a3a2a1a0⟩
  | 21 => ⟨8,0xafaeadacabaaa9a8⟩
  | 22 => ⟨8,0xb7b6b5b4b3b2b1b0⟩
  | 23 => ⟨8,0xbfbebdbcbbbab9b8⟩
  | 24 => ⟨8,0xc7c6c5c4c3c2c1c0⟩
  | 25 => ⟨8,0xc0b8786858502810⟩
  | 26 => ⟨8,0x9080795929201808⟩
  | 27 => ⟨8,0xb9a8a08860483000⟩
  | 28 => ⟨8,0xa9a1817061492a19⟩
  | 29 => ⟨8,0xaa9891514a400901⟩
  | 30 => ⟨8,0xc1a2827a715a4b1a⟩
  | 31 => ⟨8,0xab99895b38211b11⟩
  | 32 => ⟨8,0xc2bab08a83726231⟩
  | 33 => ⟨8,0xbbac736963322b22⟩
  | 34 => ⟨8,0x8b844c332c230a02⟩
  | 35 => ⟨8,0xa38c855241391c0b⟩
  | 36 => ⟨8,0xb1a47b746a533a0c⟩
  | 37 => ⟨8,0xb2a59a928d5c3403⟩
  | 38 => ⟨8,0xb3936b5d3b241204⟩
  | 39 => ⟨8,0xbcb49b643c352d13⟩
  | 40 => ⟨8,0xad9c94866c54420d⟩
  | 41 => ⟨8,0xbdb56d655e432e0e⟩
  | 42 => ⟨8,0xc3ae957c6e3d1d14⟩
  | 43 => ⟨8,0xc49d9655443e0f05⟩
  | 44 => ⟨8,0xc5be87564d2f1506⟩
  | 45 => ⟨8,0xaf9e978e7d665f4e⟩
  | 46 => ⟨8,0xc6a6755736251607⟩
  | 47 => ⟨8,0xc7b67e674f45261e⟩
  | 48 => ⟨8,0x9f8f766f463f1f17⟩
  | 49 => ⟨8,0xbfb7a77f77473727⟩
  | 50 => ⟨6,0x819610248040⟩
  | 51 => ⟨6,0x8e285b691282⟩
  | 52 => ⟨6,0x91c4d230b103⟩
  | 53 => ⟨5,0xed68f734c5⟩
  | 54 => ⟨6,0x9e695f797587⟩
  | 55 => ⟨7,0x952644060a94a8⟩
  | 56 => ⟨7,0x992dc3364c562b⟩
  | 57 => ⟨7,0x82f1dba72d5a2d⟩
  | 58 => ⟨7,0x9b121c27cf57ae⟩
  | 59 => ⟨7,0x9f3a3c68afdbb6⟩
  | 60 => ⟨7,0xe1a30e0b3628d0⟩
  | 61 => ⟨7,0xe7cb8e9c78adda⟩
  | 62 => ⟨7,0xe9af564bb729d2⟩
  | 63 => ⟨7,0xddb7665bd5aad4⟩
  | 64 => ⟨7,0xefdbaefcf9afd7⟩
  | 65 => ⟨8,0x9891908881807978⟩
  | 66 => ⟨8,0x998b8a898483827a⟩
  | 67 => ⟨8,0x9b9a93928d8c857b⟩
  | 68 => ⟨8,0x9d9c96959487867c⟩
  | 69 => ⟨8,0x9f9e978f8e7f7e7d⟩
  | 70 => ⟨8,0xc0b9b8aaa9a8a1a0⟩
  | 71 => ⟨8,0xc2c1bbbab0acaba2⟩
  | 72 => ⟨8,0xbcb4b3b2b1a5a4a3⟩
  | 73 => ⟨8,0xc5c4c3bebdb5aead⟩
  | 74 => ⟨8,0xc7c6bfb7b6afa7a6⟩
  | _ => ⟨1,0⟩

def pattern : Pattern 200 8 where
  color i := Fin.ofNat 8 ((bases 0)[i.val]!)
  pin i := (pins 0)[i.val]! == 1
  line i k := (lines k.val)[i.val]!
  group u k := Fin.ofNat 200 ((groups (u.val%75))[k.val]!)

theorem clique : ∀ u i j,i≠j → Near pattern (pattern.group u i) (pattern.group u j) := by decide +kernel
end Activated.Core005
