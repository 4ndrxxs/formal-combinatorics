import SignedBudgetCertificate
import SignedRequiredAnchor
import SignedMultiplierOrbits

namespace Signed39.Contraction

open Finset Template

local instance : Fact (Nat.Prime 31) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private def W (x:ZMod 31) : ℤ := ([0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 1, 0, 0, 2, 2, 1, 0, 0, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1]:List ℤ).getD x.val 0
private def types : List RowType := [((-22),50),((-22),112),((-21),69),((-20),90),((-19),51),((-19),113),((-18),76),((-17),41),((-17),103),((-16),70),((-15),39),((-15),101),((-14),72),((-13),45),((-13),107),((-12),82),((-11),59),((-11),121),((-10),38),((-10),100),((-9),81),((-8),64),((-7),49),((-7),111),((-6),36),((-6),98),((-5),87),((-4),78),((-3),71),((-2),66),((-1),63),((-1),125),(0,0),(0,62),(0,124),(1,63),(1,125),(2,66),(3,71),(4,78),(5,87),(6,36),(6,98),(7,49),(7,111),(8,64),(9,81),(10,38),(10,100),(11,59),(11,121),(12,82),(13,45),(13,107),(14,72),(15,39),(15,101),(16,70),(17,41),(17,103),(18,76),(19,51),(19,113),(20,90),(21,69),(22,50),(22,112),(23,95),(24,80),(25,67),(26,56),(26,118),(27,47),(27,109),(28,102),(29,97),(30,94),(31,93),(32,94)]
private def cuts : Stage := [  (((-22),50),⟨⟨0,(-128557),0,0⟩,[],903⟩),
  (((-22),112),⟨⟨0,(-1480250),86250,111344⟩,[],21⟩),
  (((-19),51),⟨⟨0,(-7626),0,0⟩,[],23⟩),
  (((-19),113),⟨⟨0,(-1050125),13750,42391⟩,[],161⟩),
  (((-16),70),⟨⟨0,(-1744),0,0⟩,[],1⟩),
  (((-13),45),⟨⟨0,(-1271),0,0⟩,[],4⟩),
  (((-13),107),⟨⟨0,(-44225300600000),2604524812500,2149695000000⟩,[],2339285637⟩),
  (((-10),38),⟨⟨0,(-36107950),0,1444318⟩,[],5125⟩),
  (((-10),100),⟨⟨0,(-198432072860617),16236770714008,7187893534532⟩,[],9742063224⟩),
  (((-7),49),⟨⟨0,(-7378),0,0⟩,[],9⟩),
  (((-7),111),⟨⟨0,(-213657793743295),14106438598065,7522918617410⟩,[],22415715476⟩),
  (((-4),78),⟨⟨0,(-177599586536777),0,4138361044349⟩,[],101880992920⟩),
  (((-1),63),⟨⟨0,(-2000000),0,64000⟩,[],191⟩),
  (((-1),125),⟨⟨0,(-1000000),0,32000⟩,[],83⟩),
  ((2,66),⟨⟨0,(-4000000),0,256000⟩,[],203⟩),
  ((5,87),⟨⟨0,(-17335525),0,693421⟩,[],4250⟩),
  ((8,64),⟨⟨0,(-4287781625),0,96795000⟩,[],1375146⟩),
  ((11,59),⟨⟨217000,(-875750),0,48732⟩,[],77⟩),
  ((11,121),⟨⟨0,(-968750),8625,53809⟩,[],74⟩),
  ((14,72),⟨⟨0,(-615350),0,20026⟩,[],261⟩),
  ((17,41),⟨⟨0,(-682),0,0⟩,[],1⟩),
  ((17,103),⟨⟨0,(-468875),1125,40942⟩,[],18⟩),
  ((20,90),⟨⟨0,(-387500),5625,30025⟩,[],16⟩),
  ((23,95),⟨⟨0,(-294679068564455),5645068581990,17905119397452⟩,[],17648961540⟩),
  ((26,56),⟨⟨0,(-620),0,0⟩,[],1⟩),
  ((26,118),⟨⟨0,(-3083312803555500),392096874792500,117556148323125⟩,[],39637874394⟩),
  ((29,97),⟨⟨0,(-34875),0,2511⟩,[],1⟩),
  ((32,94),⟨⟨0,(-2697),0,0⟩,[],1⟩)]
private theorem proof0 : ∀w∈(cuts.drop 0).take 5,w.2.valid 31 125 781 6 25 5 121 types w.1 := by decide +kernel
private theorem proof1 : ∀w∈(cuts.drop 5).take 5,w.2.valid 31 125 781 6 25 5 121 types w.1 := by decide +kernel
private theorem proof2 : ∀w∈(cuts.drop 10).take 5,w.2.valid 31 125 781 6 25 5 121 types w.1 := by decide +kernel
private theorem proof3 : ∀w∈(cuts.drop 15).take 5,w.2.valid 31 125 781 6 25 5 121 types w.1 := by decide +kernel
private theorem proof4 : ∀w∈(cuts.drop 20).take 5,w.2.valid 31 125 781 6 25 5 121 types w.1 := by decide +kernel
private theorem proof5 : ∀w∈(cuts.drop 25).take 5,w.2.valid 31 125 781 6 25 5 121 types w.1 := by decide +kernel
private theorem allCuts : ∀w∈cuts,w.2.valid 31 125 781 6 25 5 121 types w.1 := by
  have round : cuts=((cuts.drop 0).take 5 ++ ((cuts.drop 5).take 5 ++ ((cuts.drop 10).take 5 ++ ((cuts.drop 15).take 5 ++ ((cuts.drop 20).take 5 ++ (cuts.drop 25).take 5))))) := by rfl
  rw [round]; simp only [List.forall_mem_append]
  exact ⟨proof0,proof1,proof2,proof3,proof4,proof5⟩


private theorem on_product {H:Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (hm:Fintype.card H=125)
    {f:ZMod 31×H→ℤ} (hf:IsSDS 781 6 f) (ms:mass f=155) : False := by
  have hdr:shortHeader 31 125 27 2 1 0 781 6 25 5 18 29 := by decide +kernel
  have cover: shortCover 31 125 27 2 1 781 6 25 5 18 (fun b=>b∈types) := by decide +kernel
  have all:=short_cover_sound hm hdr cover hf ms
  obtain ⟨c,hc,_,mu,fu⟩:=centered_row_corr (s:=25) hf (by decide)
  rw [ms] at hc
  have cc:c=5:=by omega
  subst c
  have lev : ∀x:ZMod 31,(3:ℤ)∣(if x=0 then (0:ℤ) else 1)+W ((5:ZMod 31)^2*x)-W x := by decide +kernel
  obtain ⟨i,div⟩:=centered_anchor_residue (p:=31) (q:=5) 2 3 3 (fun x=>rowMass f x-5) W mu fu
    (by decide) (by decide) (by decide) (by decide) (by decide) lev
  have choose : ∀a∈types,(3:ℤ)∣a.1-5 → a∈cuts.map Prod.fst := by decide +kernel
  obtain ⟨⟨a,h⟩,hmk,eq⟩:=List.mem_map.mp (choose (rowType f i) (all i) div)
  have bad:=excluded_anchor hf (by decide : (781:ℤ)-6=31*25) (by decide) ms hm (by decide) (w:=30)
    (by decide : (31:ℤ)*121=1+125*30) all (allCuts (a,h) hmk) i
  exact bad eq.symm

theorem reduced_3875_781 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=3875) :
    ¬∃f:G→ℤ,IsSDS 781 6 f := by
  classical
  rintro ⟨f,hf⟩
  obtain ⟨K,hK,⟨E⟩⟩:=split_prime_factor (p:=31) (m:=125) hg (by decide)
  have hm:Fintype.card (Additive K)=125:=Nat.card_eq_fintype_card.symm.trans hK
  have h:=pullback hf E
  have total:=sds_mass h
  rw [Fintype.card_prod,ZMod.card,hm] at total
  have sq:(mass (fun x=>f (E x)))^2=155^2 := by norm_num at total ⊢; exact total
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp sq with pos|neg
  · exact on_product hm h pos
  · exact on_product hm h.neg (by simpa only [mass,sum_neg_distrib,neg_eq_iff_eq_neg] using neg)

#print axioms reduced_3875_781

end Signed39.Contraction

