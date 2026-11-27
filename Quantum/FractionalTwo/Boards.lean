module
public import Quantum.FractionalBinary

@[expose] public section
namespace FractionalTwo
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def boardNumberBlock (j : ℕ) : ℕ :=
  if j<9 then
    if j<4 then
      if j<2 then
        if j<1 then
          0x63c91eb44be11eb4e11b4eb41be14eb4b14e1be48d721be4728d1be44eb11be4b11e4be41eb14be4b14b1ee44bb11ee4b11b4ee439934ee493394ee41bb14ee4
        else
          0x2d7287d8722d87d872872dd887722dd872278dd836638dd863368dd827728dd8e14e1bb44ee11bb4e11e4bb42dd24bb4d22d4bb41ee14bb4e14b1eb4c9631eb4
      else
        if j<3 then
          0x8dd22778d28d2778e11e87782dd28778d22d87781ee18778d2872d78c6932d7893c62d7887d22d78d2278d7827d28d78b14e27d88d7227d8728d27d84eb127d8
        else
          0x93c6396c87d2396c3693c96c9336c96ce14b369cc963369c63c9369c4be1369c3963c69c6339c69cc663399c63c6399c7227c99c3663c99c6336c99c2772c99c
    else
      if j<6 then
        if j<5 then
          0x369c4be11eb44be1b44b1ee178871ee187781ee14bb41ee1b41b4ee11bb44ee1c993366c93c9366cb11bc66c3993c66c9339c66c1bb1c66cd287396cc693396c
        else
          0xe44e1bb16cc61bb1c66c1bb14ee41bb1e41e4bb11ee44bb1e44b1eb14be41eb1e41b4eb1d8274eb127d84eb11be44eb1b44e1be14eb41be1b41e4be19c364be1
      else
        if j<7 then
          0x93c66c3987d26c39c6639c3963c69c39b41e63c99c3663c9369c63c91eb463c96c3693c9366c93c936936cc993366cc972279cc936639cc963369cc927729cc9
        else
          if j<8 then
            0x7827d28d2778d28dd227788d27d2788d7227d88d3663d88d6336d88d2772d88d9cc66339c69c6339e44e93396cc69339c66c93394ee49339d2876c39c6936c39
          else
            0xd887722d87d8722db44bd22d7887d22d8778d22d4bb4d22dd287782dc693782d93c6782d87d2782d7287d82d8772d82de41b728dd827728d27d8728d1be4728d
  else
    if j<13 then
      if j<11 then
        if j<10 then
          0xe41b8d72d8278d7227d88d721be48d72788d27d28d7827d2782d87d26c3987d2396c87d22d7887d2b44b2dd278872dd287782dd24bb42dd278278dd227788dd2
        else
          0x396c93c62d7893c6b11b6cc639936cc693396cc61bb16cc639639cc663399cc6d88d27729cc92772c99c27728dd82772d82d87722dd88772d8872d7287d82d72
      else
        if j<12 then
          0xd88d63369cc96336c99c63368dd863366cc99336c96c9336c9936c3693c96c36e14b9c36c9639c3663c99c364be19c369c3963c6399c63c6782d93c66c3993c6
        else
          0x63c9b41e4be1b41eb14be41e4bb1e41ee41bb14ed827b14e27d8b14e1be4b14eb41be14e1bb4e14ee11bb44e1be1b44eb11be44e3993e44e9339e44e1bb1e44e
    else
      if j<15 then
        if j<14 then
          0x396cc6932d78c693e44e39936cc63993c66c39934ee439936c36c993366cc993e44bb11e4be4b11eb44be11e7887e11e8778e11e4bb4e11ee14bb41ec963b41e
        else
          0xd88d36639cc93663c99c36638dd836639c39c663399cc6639cc63963c69c3963b41ec9639c36c963369cc9631eb4c9636cc93693c96c3693782dc6936c39c693
      else
        if j<16 then
          0xb14ed8278d72d827728dd8274eb1d827d82d72872dd87287782dd2876c39d287396cd2872d78d287e11e78872dd27887d22d78871ee178872d72d887722dd887
        else
          if j<17 then
            0x369ce14b1eb4e14be11eb44b2dd2b44bd22db44b1ee1b44bb11ee44b1eb1e44bd88d72279cc97227c99c72278dd87227788dd2278d78d2278dd27827d28d7827
          else
            0xe44eb11b6cc6b11bc66cb11b4ee4b11bb44ee11b4eb4e11be14eb41b4ee1b41bb14ee41b8d72e41b728de41b4eb1e41be41eb14b1ee4b14bb41ee14b9c36e14b

def boardNumber (i : ℕ) : ℕ := (boardNumberBlock (i/16) >>> (32*(i%16))) % (2^32)

def candidate (j : Fin 288) (s : FractionalBinary.Site) : Fin 4 :=
  Fin.ofNat 4 ((boardNumber j.val >>> (2*(4*s.1.val+s.2.val))))
theorem candidate_injective : ∀ (j : Fin 288) (l : Fin 12) (a b : Fin 4),
    candidate j (FractionalBinary.line l a)=candidate j (FractionalBinary.line l b) → a=b := by
  decide +kernel
end FractionalTwo
