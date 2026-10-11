import SunFourDeletion.Statement
import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

def goodNine : Fin 5 → ZMod 9 := ![4,5,6,7,8]
def badNine : Fin 5 → ZMod 9 := ![4,5,6,8,7]

theorem goodNine_valid : RainbowEnumeration (by decide : 0<5)
    ({0,1,2,3}ᶜ : Set (ZMod 9)) goodNine := by
  refine ⟨by decide,?_,by decide⟩
  ext x
  have h : ∀ x : ZMod 9, (∃ i : Fin 5, goodNine i=x) ↔ x≠0 ∧ x≠1 ∧ x≠2 ∧ x≠3 := by decide
  simpa only [Set.mem_range,Set.mem_compl_iff,Set.mem_insert_iff,
    Set.mem_singleton_iff,not_or] using h x

theorem badNine_vertices_and_internal_sums :
    Function.Injective badNine ∧
    Set.range badNine = ({0,1,2,3}ᶜ : Set (ZMod 9)) ∧
    Function.Injective (fun i : Fin 4 => badNine i.castSucc + badNine i.succ) := by
  refine ⟨by decide,?_,by decide⟩
  ext x
  have h : ∀ x : ZMod 9, (∃ i : Fin 5, badNine i=x) ↔ x≠0 ∧ x≠1 ∧ x≠2 ∧ x≠3 := by decide
  simpa only [Set.mem_range,Set.mem_compl_iff,Set.mem_insert_iff,
    Set.mem_singleton_iff,not_or] using h x

/-- The internal sums are distinct, but the closing sum repeats the edge at index 1. -/
theorem badNine_closing_collision :
    badNine 1 + badNine (cyclicSuccessor (by decide) 1) =
    badNine 4 + badNine (cyclicSuccessor (by decide) 4) := by
  decide

theorem badNine_rejected : ¬ RainbowEnumeration (by decide : 0<5)
    ({0,1,2,3}ᶜ : Set (ZMod 9)) badNine := by
  intro h
  exact (by decide : (1 : Fin 5) ≠ 4) (h.2.2 badNine_closing_collision)

#print axioms goodNine_valid
#print axioms badNine_rejected

end SunFourDeletion
