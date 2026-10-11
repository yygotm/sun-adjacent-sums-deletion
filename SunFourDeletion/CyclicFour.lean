import SunFourDeletion.OddCyclic

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion

theorem cyclic_four_cycle (G : Type*) [AddCommGroup G] [Finite G] [IsAddCyclic G]
    (hodd : Odd (Nat.card G)) (hsize : 7≤Nat.card G) (D : Finset G) (hD : D.card=4) :
    HasRainbowCycle ((D : Set G)ᶜ) := by
  classical
  letI := Fintype.ofFinite G
  have hc : Dᶜ.card=Nat.card G-4 := by
    rw [Finset.card_compl,hD,Nat.card_eq_fintype_card]
  have ho : Odd Dᶜ.card := by
    obtain ⟨k,hk⟩ := hodd
    refine ⟨k-2,?_⟩
    omega
  have hh := odd_cyclic_subset G Dᶜ ho (by omega)
  simpa using hh

end SunFourDeletion
