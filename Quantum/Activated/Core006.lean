module
public import Quantum.Activated.Constraints
public import Quantum.FractionalImpossibleTables

@[expose] public section
namespace Activated.Core006
open ImpossibleSudoku
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bases : ℕ → Packed
  | 0 => ⟨3,0x2c5f16650d67177662d17ac8c989e9f0ea98ab9d032ea1f411d2b7d0bf505f02ec133e6aac633a62cf91055f1ed3b3509d614b47e8c5159de2b8f883b1760e8730af7d0d294787aca53987d7a223614a7e878756f31ad0632f0dbd6843f5e8812ea1a7c84ecd98b17a9d0c5d⟩
  | _ => ⟨1,0⟩

def pins : ℕ → Packed
  | 0 => ⟨1,0x1d0e62d88ad8ac2352ed63e6906cffcedebbc9d1d1eb4e278de219a5e82ddcdb2791eedd⟩
  | _ => ⟨1,0⟩

def lines : ℕ → Packed
  | 0 => ⟨6,0x8e38e38e38e38a28a28a28a28618618618618208208208207df7df7df7df79e79e79e79e75d75d75d75d71c71c71c71c6db6db6db6db69a69a69a69a6596596596596186186186185d75d75d75d75965965965965555555555555145145145144d34d34d34d34924924924924514514514514104104104103cf3cf3cf3cf38e38e38e38e34d34d34d34d30c30c30c30c2cb2cb2cb2cb28a28a28a28a2492492492492082082082081c71c71c71c71861861861861451451451451041041041040c30c30c30c3082082082082041041041041000000000000⟩
  | 1 => ⟨6,0x8e285e5543c375758f28204075a40f2481c28a179b44e3497194d238b20589b65650a1438184d038d2c081e6574502488195d328810185f71b68f3048a175348c1827134871840407da5cf30b14381f6113471836984c91c50c28185d65523818a071a38c1c68e165448d1c48d751134918475550e30b14485a5122ca2418df79c5503847de75b6562c07db6103c814089d6d240c2037dc51238d2888e285758b20081e7594502468dc6161c20406564d13040808d65513c60817db54b2471818a154d3050c28e07954503ca75b69850d28579c6985d3283⟩
  | 2 => ⟨6,0x8e38e386181e8a18607de79e8a28207df7de8e38e282081f8a286181f7de8e28a185f79e75c6da69a65875d71b69a65975c6db65961875d71c71a69875d71b6da65871b6d96586185d65545134925d75945134d25965534d24925d65555555125d75965144d35d75955544d244f3ce38d34c40f3ce38d30c4503cf34d34c4514503ce38c45141040f34c45040e38d30c2ca2892081c62ca2492081c72cb2c92471c62cb28a2081c72ca2891c61862892482061861430c20810001440c10410401450c20800001451430820811041040c20401441040c3040⟩
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
  | 25 => ⟨8,0xcfcecdcccbcac9c8⟩
  | 26 => ⟨8,0xd7d6d5d4d3d2d1d0⟩
  | 27 => ⟨8,0xdfdedddcdbdad9d8⟩
  | 28 => ⟨8,0xe7e6e5e4e3e2e1e0⟩
  | 29 => ⟨8,0xefeeedecebeae9e8⟩
  | 30 => ⟨8,0xf7f6f5f4f3f2f1f0⟩
  | 31 => ⟨8,0xfffefdfcfbfaf9f8⟩
  | 32 => ⟨9,0x83c1a0b0481c0a0300⟩
  | 33 => ⟨9,0x87c3a1b0c85c2a1308⟩
  | 34 => ⟨9,0x8bc5a2b1489c4a2310⟩
  | 35 => ⟨9,0x8fc7a3b1c8dc6a3318⟩
  | 36 => ⟨9,0x883a18068301207030⟩
  | 37 => ⟨9,0x88b6182a03c0e45020⟩
  | 38 => ⟨9,0x8942190a81d0c45218⟩
  | 39 => ⟨9,0x8c3c170b0549603200⟩
  | 40 => ⟨8,0xd9d0c29088807032⟩
  | 41 => ⟨8,0xf8f1b9aa81611a08⟩
  | 42 => ⟨8,0xc9c3b19889402a21⟩
  | 43 => ⟨9,0x84b1164ab4ca447622⟩
  | 44 => ⟨9,0x853e5c0da31164a049⟩
  | 45 => ⟨9,0x85c01c2ac451e48223⟩
  | 46 => ⟨9,0x89bc9b67a288401201⟩
  | 47 => ⟨8,0xfae9ba827b694a24⟩
  | 48 => ⟨8,0xd1cabb9a835a331b⟩
  | 49 => ⟨9,0x80ba9669245948380a⟩
  | 50 => ⟨9,0x813edd6a14da10e253⟩
  | 51 => ⟨9,0x8cc5218d25e18c5611⟩
  | 52 => ⟨9,0x86bb1c4723216c8412⟩
  | 53 => ⟨9,0x81b8d688c218d05813⟩
  | 54 => ⟨8,0xfccbc5a2937c5c54⟩
  | 55 => ⟨8,0xfdeddcccc6ad3502⟩
  | 56 => ⟨9,0x8d3cd288d429f4aa0b⟩
  | 57 => ⟨9,0x8da8d0c73168943a14⟩
  | 58 => ⟨9,0x8abd1486a258f06c2e⟩
  | 59 => ⟨9,0x8b391babd52a389803⟩
  | 60 => ⟨8,0xeeb5aea6653d0c04⟩
  | 61 => ⟨8,0xfef5e5de956b4437⟩
  | 62 => ⟨9,0x8734d7caf4e1f81a05⟩
  | 63 => ⟨9,0x823d9a86c331744c0e⟩
  | 64 => ⟨8,0xffd5c79d74563e06⟩
  | 65 => ⟨9,0x8bc3d9a87369788a0f⟩
  | 66 => ⟨9,0x8e415cc75371182a07⟩
  | 67 => ⟨8,0xd6bfb6766f675727⟩
  | 68 => ⟨8,0xefe7dfb7a79e4716⟩
  | 69 => ⟨9,0x8ec19aece4b1fc9a1e⟩
  | 70 => ⟨9,0x8f41deecf4f97c9c1f⟩
  | 71 => ⟨9,0x8fa5d1e77278fc5e17⟩
  | 72 => ⟨6,0xa6881a658200⟩
  | 73 => ⟨6,0xaa48e2850241⟩
  | 74 => ⟨6,0xb2b71b4d244a⟩
  | 75 => ⟨6,0xbad95d50b0c2⟩
  | 76 => ⟨6,0x98f38d306144⟩
  | 77 => ⟨6,0xbe77de5d6547⟩
  | 78 => ⟨7,0xb121d3970c98b0⟩
  | 79 => ⟨7,0xb34684a930603b⟩
  | 80 => ⟨7,0xb76a9d28709a33⟩
  | 81 => ⟨7,0xb956a4c96f1b35⟩
  | 82 => ⟨7,0xbd76b4588f9eb7⟩
  | 83 => ⟨7,0xbf5e7ce9b1e33f⟩
  | 84 => ⟨8,0x8881807870686160⟩
  | 85 => ⟨8,0x8a89827b7a796962⟩
  | 86 => ⟨8,0x8c8b848372716463⟩
  | 87 => ⟨8,0x8e8d86857d7c736a⟩
  | 88 => ⟨8,0x877e746d6c6b6665⟩
  | 89 => ⟨8,0x8f7f7776756f6e67⟩
  | 90 => ⟨8,0xb9b8b0aaa9a8a090⟩
  | 91 => ⟨8,0xbab2b1acab999891⟩
  | 92 => ⟨8,0xbcbbb4b3a19b9a92⟩
  | 93 => ⟨8,0xbdada5a4a3a29493⟩
  | 94 => ⟨8,0xbeb5afaea69d9c95⟩
  | 95 => ⟨8,0xbfb7b6a79f9e9796⟩
  | 96 => ⟨8,0xe8d9d8d0c8c2c1c0⟩
  | 97 => ⟨8,0xe9e1e0dbdac9c4c3⟩
  | 98 => ⟨8,0xecebeae3e2d2d1ca⟩
  | 99 => ⟨8,0xede4dddccccbc6c5⟩
  | 100 => ⟨8,0xeee5ded5d4d3cdc7⟩
  | 101 => ⟨8,0xefe7e6dfd7d6cfce⟩
  | 102 => ⟨9,0x8c44a2310843e1e2f0⟩
  | 103 => ⟨9,0x89c2e1509803e9f2f2⟩
  | 104 => ⟨9,0x8cc521b0c81c0a02fb⟩
  | 105 => ⟨9,0x8dc6a2d157ebf1e8f3⟩
  | 106 => ⟨9,0x8bc3e1d047fbf9ecf5⟩
  | 107 => ⟨9,0x8fc7a3b1c83c1a0af7⟩
  | _ => ⟨1,0⟩

def pattern : Pattern 288 8 where
  color i := Fin.ofNat 8 ((bases 0)[i.val]!)
  pin i := (pins 0)[i.val]! == 1
  line i k := (lines k.val)[i.val]!
  group u k := Fin.ofNat 288 ((groups (u.val%108))[k.val]!)

theorem clique : ∀ u i j,i≠j → Near pattern (pattern.group u i) (pattern.group u j) := by decide +kernel
end Activated.Core006
