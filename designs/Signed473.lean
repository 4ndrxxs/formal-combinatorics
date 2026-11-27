import Signed473Block0
import Signed473Block8
import Signed473Block16
import Signed473Block24

namespace Signed39.Template

def templates (n:Fin 32) : Case := match n.val with
  | 0 => template0
  | 1 => template1
  | 2 => template2
  | 3 => template3
  | 4 => template4
  | 5 => template5
  | 6 => template6
  | 7 => template7
  | 8 => template8
  | 9 => template9
  | 10 => template10
  | 11 => template11
  | 12 => template12
  | 13 => template13
  | 14 => template14
  | 15 => template15
  | 16 => template16
  | 17 => template17
  | 18 => template18
  | 19 => template19
  | 20 => template20
  | 21 => template21
  | 22 => template22
  | 23 => template23
  | 24 => template24
  | 25 => template25
  | 26 => template26
  | 27 => template27
  | 28 => template28
  | 29 => template29
  | 30 => template30
  | _ => template31

theorem all_checked (n:Fin 32) : checked (templates n) n := by
  fin_cases n
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18
  · exact checked19
  · exact checked20
  · exact checked21
  · exact checked22
  · exact checked23
  · exact checked24
  · exact checked25
  · exact checked26
  · exact checked27
  · exact checked28
  · exact checked29
  · exact checked30
  · exact checked31

theorem no_473_265_12 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=473) :
    ¬∃f:G→ℤ,IsSDS 265 12 f := no_473_of_templates G hg templates all_checked

#print axioms no_473_265_12

end Signed39.Template
