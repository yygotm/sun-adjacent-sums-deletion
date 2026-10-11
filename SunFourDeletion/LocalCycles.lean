import SunFourDeletion.OneHole
import SunThreeDeletion.Main

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem retained_card (D : Finset G) : Nat.card {x : G // x∉D}=Nat.card G-D.card := by
  classical
  letI := Fintype.ofFinite G
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_coe]

/-- The already established 0,1,2,3 deletion results, with the exact local size bound. -/
theorem small_deletion_cycle (hodd : Odd (Nat.card G)) (D : Finset G)
    (hD : D.card≤3) (hsize : 3≤Nat.card G-D.card) : HasRainbowCycle ((D : Set G)ᶜ) := by
  classical
  have hh : D.card=0 ∨ D.card=1 ∨ D.card=2 ∨ D.card=3 := by omega
  rcases hh with hh | hh | hh | hh
  · have he : D=∅ := Finset.card_eq_zero.mp hh
    haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨x,hx⟩ := exists_ne (0 : G)
    obtain ⟨C,_⟩ := edge_property_odd G hodd x 0 hx
    simpa [he] using (show HasRainbowCycle (Set.univ : Set G) from ⟨C⟩)
  · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp hh
    have hN : 5≤Nat.card G := by obtain ⟨k,hk⟩ := hodd; simp only [Finset.card_singleton] at hsize; omega
    simpa using one_hole G hodd hN a
  · obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hh
    obtain ⟨C,_⟩ := sun_two_deletion_exact G hodd (by omega) a b hab
    simpa using (show HasRainbowCycle ({a,b}ᶜ : Set G) from ⟨C⟩)
  · obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hh
    simpa using three_deletion_cycle hodd (by omega) a b c hab hac hbc

end SunFourDeletion
