import SunThreeDeletion.QCycle
import SunTwoDeletion.Map
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

theorem one_hole_cyclic_group (G : Type*) [AddCommGroup G] [Finite G] [IsAddCyclic G]
    (hodd : Odd (Nat.card G)) (hcard : 5 ≤ Nat.card G) :
    HasRainbowCycle ({0}ᶜ : Set G) := by
  obtain ⟨C,_⟩ := cyclic_one_deletion (Nat.card G) hodd hcard
  let e : ZMod (Nat.card G) ≃+ G := zmodAddCyclicAddEquiv (inferInstance : IsAddCyclic G)
  have h := C.map e.toAddMonoidHom e.injective
  have he : e '' ({0}ᶜ : Set (ZMod (Nat.card G))) = ({0}ᶜ : Set G) := by
    rw [Set.image_compl_eq e.bijective]
    simp
  exact ⟨he ▸ h⟩

end SunThreeDeletion

