module
public import Quantum.Activated.Constraints
public import Quantum.FractionalImpossibleTables

@[expose] public section
namespace Activated.Core007
open ImpossibleSudoku
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bases : ℕ → Packed
  | 0 => ⟨3,0x1d56d36490240c28366805a40b4cc8c5755b4d92409030a0d9a016902d332315d56d36490240c28366805a40b4cc8c5755b4d92409030a0d9a016902d332315d56d36490240c28366805a40b4cc8c5755b4d92409030a0d9a016902d332315d56d36490240c28366805a40b4cc8c5⟩
  | _ => ⟨1,0⟩

def pins : ℕ → Packed
  | 0 => ⟨1,0x173caa800005cf2aa0000173caa800005cf2aa0000173caa800005cf2aa0000173caa80000⟩
  | _ => ⟨1,0⟩

def lines : ℕ → Packed
  | 0 => ⟨6,0xc2fbadb2bab0beeb6caeac30c30befbefbaebaeb6db6db2cb2caebaebaaaaaaa689e69648e9a279a5923a69a69a28a289e79e79a69a69659659249248e38e38a181f79d7228607de75c8a28a28618618208207df7df79e79e75d75d71c71c6da6585d655b6996175956db6db69a69a6596596186185d75d759659655555551349140f3944d24503ce5145144d34d34924924514514104103cf3cf38e38e34c2ca2481cd30b28920734d34d30c30c2cb2cb28a28a2492492082081c71c71851030810061440c20401861861451451041040c30c3082082041041000000⟩
  | 1 => ⟨6,0x888098be7394304b65755c1bbdd88ab23be678714b4244e708880358e6d9440a4f25f16e55b4cb0ec91c1a2164a510aa16d94e3125eb6ae24f9ca7558a0607c16426304722692282ae336932bc18240303b154d9781844416b9191ca677ce19d5ed4cb8e985944906a5304c119f4074ca09c6a0948a0b5dd118ae3c2e995364783692ab0a206102006c66883665ce691263867b0fbd27a42df06a184b5c52b94a859006be77d73c788d84f52d79585842aa2e09615996b4a620034b0e36c1b11a201cd16e99e58ea54a166c395ca1f5c0bc425d320b0166d3c75122aa⟩
  | 2 => ⟨6,0xbabaadc2fb2caeac2fbadc2dc2ebabc2fc2fbabaabb2fb2faabbaab6cb6db2aa259278e99a69648e9a278e78e8a258e98e9a259259a99a9925a249e69e79a489f7a175c8207de75c8a176176289f75c75c89f79f81c81c79f89e86086181e55961b5d669a6585d655b5db5d55595d65d65596196966966195586da6db6983d348e4505144d24503ce44e44f3d34504503d34935105104933d239438e51224d3082ca1c734c2ca2482c82c924d2ca2ca24d30d1ca1ca30d24c2072081cc0c01821440410061440c21421430c01441440c01800440441800c6081082046⟩
  | _ => ⟨1,0⟩

def groups : ℕ → Packed
  | 0 => ⟨6,0x8dc0c2040⟩
  | 1 => ⟨6,0x91d1c6144⟩
  | 2 => ⟨6,0x95e2ca248⟩
  | 3 => ⟨6,0x99f3ce34c⟩
  | 4 => ⟨6,0x9e04d2450⟩
  | 5 => ⟨6,0xa215d6554⟩
  | 6 => ⟨6,0xa626da658⟩
  | 7 => ⟨7,0x26c65ab15aa⟩
  | 8 => ⟨7,0x274762c17ae⟩
  | 9 => ⟨7,0x27c86ad19b2⟩
  | 10 => ⟨7,0x284972e1bb6⟩
  | 11 => ⟨7,0x28ca7af1dba⟩
  | 12 => ⟨7,0x294b8301fbe⟩
  | 13 => ⟨7,0x29cc8b121c2⟩
  | 14 => ⟨7,0x3bf0af5aad4⟩
  | 15 => ⟨7,0x3c71b76acd8⟩
  | 16 => ⟨7,0x3cf2bf7aedc⟩
  | 17 => ⟨7,0x3d73c78b0e0⟩
  | 18 => ⟨7,0x3df4cf9b2e4⟩
  | 19 => ⟨7,0x3e75d7ab4e8⟩
  | 20 => ⟨7,0x3ef6dfbb6ec⟩
  | 21 => ⟨8,0xa19a81807f7e⟩
  | 22 => ⟨8,0xa29b85848382⟩
  | 23 => ⟨8,0xa39c89888786⟩
  | 24 => ⟨8,0xa49d8d8c8b8a⟩
  | 25 => ⟨8,0xa59e91908f8e⟩
  | 26 => ⟨8,0xa69f95949392⟩
  | 27 => ⟨8,0xa7a099989796⟩
  | 28 => ⟨8,0xcbc4abaaa9a8⟩
  | 29 => ⟨8,0xccc5afaeadac⟩
  | 30 => ⟨8,0xcdc6b3b2b1b0⟩
  | 31 => ⟨8,0xcec7b7b6b5b4⟩
  | 32 => ⟨8,0xcfc8bbbab9b8⟩
  | 33 => ⟨8,0xd0c9bfbebdbc⟩
  | 34 => ⟨8,0xd1cac3c2c1c0⟩
  | 35 => ⟨8,0xf5eed5d4d3d2⟩
  | 36 => ⟨8,0xf6efd9d8d7d6⟩
  | 37 => ⟨8,0xf7f0dddcdbda⟩
  | 38 => ⟨8,0xf8f1e1e0dfde⟩
  | 39 => ⟨8,0xf9f2e5e4e3e2⟩
  | 40 => ⟨8,0xfaf3e9e8e7e6⟩
  | 41 => ⟨8,0xfbf4edecebea⟩
  | 42 => ⟨9,0x23f187fbf9fafc⟩
  | 43 => ⟨9,0x2411981c0a0300⟩
  | 44 => ⟨9,0x2431a83c1a0b04⟩
  | 45 => ⟨9,0x2451b85c2a1308⟩
  | 46 => ⟨9,0x2471c87c3a1b0c⟩
  | 47 => ⟨9,0x2491d89c4a2310⟩
  | 48 => ⟨9,0x24b1e8bc5a2b14⟩
  | 49 => ⟨8,0xfcbc704d2e10⟩
  | 50 => ⟨8,0xb49b96592808⟩
  | 51 => ⟨9,0x2470573b191e37⟩
  | 52 => ⟨9,0x204f15d1e85616⟩
  | 53 => ⟨9,0x238cc59214ac0e⟩
  | 54 => ⟨9,0x216f775b946a21⟩
  | 55 => ⟨8,0xeda7956e574c⟩
  | 56 => ⟨9,0x218d2491184604⟩
  | 57 => ⟨9,0x24904451c4d82f⟩
  | 58 => ⟨8,0xf9dbbd9c650d⟩
  | 59 => ⟨9,0x224d863a40a001⟩
  | 60 => ⟨9,0x214f251220b62c⟩
  | 61 => ⟨9,0x23ae166b05760b⟩
  | 62 => ⟨8,0xc37d6b442d22⟩
  | 63 => ⟨9,0x23f00712a0d01c⟩
  | 64 => ⟨8,0xfada60474205⟩
  | 65 => ⟨9,0x212cf58a4ce43b⟩
  | 66 => ⟨8,0xfde8ae9d6626⟩
  | 67 => ⟨8,0xe0c8785e3102⟩
  | 68 => ⟨9,0x20ef35ba8d2e91⟩
  | 69 => ⟨9,0x23c99299043403⟩
  | 70 => ⟨9,0x230f56b2e0fc3e⟩
  | 71 => ⟨9,0x202d0580d83a18⟩
  | 72 => ⟨8,0xdfa587694811⟩
  | 73 => ⟨9,0x244d35f210e63c⟩
  | 74 => ⟨8,0xfeb69e4e3407⟩
  | 75 => ⟨8,0xddc98d796d67⟩
  | 76 => ⟨9,0x22cff7a1bc5217⟩
  | 77 => ⟨8,0xeecbac8e5414⟩
  | 78 => ⟨9,0x233146ba990c0c⟩
  | 79 => ⟨9,0x21ab53d9747e1e⟩
  | 80 => ⟨8,0xf8a9945a4912⟩
  | 81 => ⟨9,0x206d4461d0480a⟩
  | 82 => ⟨8,0xb39f634f433d⟩
  | 83 => ⟨9,0x24b13763559445⟩
  | 84 => ⟨9,0x220c450a08c82a⟩
  | 85 => ⟨9,0x210ef752b4f85c⟩
  | 86 => ⟨9,0x234e3459446615⟩
  | 87 => ⟨9,0x21cce3f9a8601f⟩
  | 88 => ⟨9,0x241066caa8c44a⟩
  | 89 => ⟨8,0x897539251913⟩
  | 90 => ⟨8,0xfbe9c2aba01b⟩
  | 91 => ⟨8,0xe69a77583a00⟩
  | 92 => ⟨8,0xdec5c0835232⟩
  | 93 => ⟨9,0x222f05c9844e09⟩
  | 94 => ⟨9,0x236e4521548006⟩
  | 95 => ⟨8,0xf6dcaf803820⟩
  | 96 => ⟨9,0x243158797c960f⟩
  | 97 => ⟨9,0x22ed15fa610276⟩
  | 98 => ⟨6,0xa21590388⟩
  | 99 => ⟨6,0x8e234b101⟩
  | 100 => ⟨6,0x99c6850c2⟩
  | 101 => ⟨6,0xa5d617447⟩
  | 102 => ⟨6,0x91e51230a⟩
  | 103 => ⟨6,0x95f6d9553⟩
  | 104 => ⟨6,0x9e03c9180⟩
  | 105 => ⟨7,0x26cc6ed572b⟩
  | 106 => ⟨7,0x284688bd6ac⟩
  | 107 => ⟨7,0x29c78505db1⟩
  | 108 => ⟨7,0x27487cf1b34⟩
  | 109 => ⟨7,0x27c98b0dfbd⟩
  | 110 => ⟨7,0x28ca72cd82a⟩
  | 111 => ⟨7,0x294b80e9c32⟩
  | 112 => ⟨7,0x3d70dd66bd6⟩
  | 113 => ⟨7,0x3ef1d9af2db⟩
  | 114 => ⟨7,0x3c72d19b05e⟩
  | 115 => ⟨7,0x3cf3dfb74e7⟩
  | 116 => ⟨7,0x3df4c776d54⟩
  | 117 => ⟨7,0x3e75d59315c⟩
  | 118 => ⟨7,0x3bf6c37ec55⟩
  | 119 => ⟨8,0xa79b96958f85⟩
  | 120 => ⟨8,0xa29c92908a88⟩
  | 121 => ⟨8,0xa39d99979391⟩
  | 122 => ⟨8,0xa59e8d87847e⟩
  | 123 => ⟨8,0xa69f948e8c86⟩
  | 124 => ⟨8,0xa1a08b89827f⟩
  | 125 => ⟨8,0xa49a98838180⟩
  | 126 => ⟨8,0xccc6bcbab4b2⟩
  | 127 => ⟨8,0xcdc7c3c1bdbb⟩
  | 128 => ⟨8,0xcfc8b7b1aea8⟩
  | 129 => ⟨8,0xd0c9beb8b6b0⟩
  | 130 => ⟨8,0xcbcab5b3aca9⟩
  | 131 => ⟨8,0xcec4c2adabaa⟩
  | 132 => ⟨8,0xd1c5c0bfb9af⟩
  | 133 => ⟨8,0xf7f1edebe7e5⟩
  | 134 => ⟨8,0xf9f2e1dbd8d2⟩
  | 135 => ⟨8,0xfaf3e8e2e0da⟩
  | 136 => ⟨8,0xf5f4dfddd6d3⟩
  | 137 => ⟨8,0xf8eeecd7d5d4⟩
  | 138 => ⟨8,0xfbefeae9e3d9⟩
  | 139 => ⟨8,0xf6f0e6e4dedc⟩
  | 140 => ⟨9,0x2471c85c1604fc⟩
  | 141 => ⟨9,0x2491d894321504⟩
  | 142 => ⟨9,0x23f1e84c1e00fd⟩
  | 143 => ⟨9,0x245188b405fefe⟩
  | 144 => ⟨9,0x24b198a44e1b03⟩
  | 145 => ⟨9,0x2411a8843a1106⟩
  | 146 => ⟨9,0x2431b8bc56230f⟩
  | _ => ⟨1,0⟩

def pattern : Pattern 294 6 where
  color i := Fin.ofNat 6 ((bases 0)[i.val]!)
  pin i := (pins 0)[i.val]! == 1
  line i k := (lines k.val)[i.val]!
  group u k := Fin.ofNat 294 ((groups (u.val%147))[k.val]!)

theorem clique : ∀ u i j,i≠j → Near pattern (pattern.group u i) (pattern.group u j) := by decide +kernel
end Activated.Core007
