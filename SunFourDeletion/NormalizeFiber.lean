import SunFourDeletion.Transport
import SunFourDeletion.DeletedFibers

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem align_full_fiber (H : AddSubgroup G) (r : G) (D : Finset G)
    (v : G ⧸ H) (hv : ∀ d∈D, QuotientAddGroup.mk d≠v) :
    ∃ s : G, ∀ x∈D.map (Equiv.addRight (-s)).toEmbedding,
      (QuotientAddGroup.mk x : G ⧸ H) ≠
        (Nat.card (G ⧸ H)-1) • QuotientAddGroup.mk r := by
  obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective
    (v-(Nat.card (G ⧸ H)-1) • (QuotientAddGroup.mk r : G ⧸ H))
  refine ⟨s,?_⟩
  intro x hx he
  obtain ⟨d,hd,rfl⟩ := Finset.mem_map.mp hx
  apply hv d hd
  change (QuotientAddGroup.mk' H) (d+ -s)=_ at he
  rw [map_add,map_neg] at he
  rw [← sub_eq_add_neg] at he
  have hh := sub_eq_iff_eq_add.mp he
  have hs' : (QuotientAddGroup.mk' H) s =
      v-(Nat.card (G ⧸ H)-1) • (QuotientAddGroup.mk r : G ⧸ H) := hs
  rw [hs'] at hh
  calc
    (QuotientAddGroup.mk d : G ⧸ H) = _ := hh
    _ = v := by abel

theorem undo_translation_cycle (D : Finset G) (s : G)
    (h : HasRainbowCycle ((D.map (Equiv.addRight (-s)).toEmbedding : Set G)ᶜ)) :
    HasRainbowCycle ((D : Set G)ᶜ) := by
  have hh := translate_finset_cycle _ s h
  have he : (D.map (Equiv.addRight (-s)).toEmbedding).map (Equiv.addRight s).toEmbedding=D := by
    ext x
    simp
  rwa [he] at hh

end SunFourDeletion
