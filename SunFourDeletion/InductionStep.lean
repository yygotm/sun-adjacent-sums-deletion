import SunFourDeletion.NormalizeFiber

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

/-- The only four-deletion premise is for the subgroup H, never for the ambient G. -/
theorem four_via_large_subgroup (hodd : Odd (Nat.card G)) (H : AddSubgroup G)
    [IsAddCyclic (G ⧸ H)] (hH : 7≤Nat.card H) (hq : 3≤Nat.card (G ⧸ H))
    (D : Finset G) (hD : D.card=4)
    (v : G ⧸ H) (hv : ∀ d∈D, QuotientAddGroup.mk d≠v)
    (ih : ∀ E : Finset H, E.card=4 → HasRainbowCycle ((E : Set H)ᶜ)) :
    HasRainbowCycle ((D : Set G)ᶜ) := by
  classical
  letI := Fintype.ofFinite H
  obtain ⟨r,hgen⟩ := quotient_generator_lift H
  obtain ⟨s,hs⟩ := align_full_fiber H r D v hv
  let E := D.map (Equiv.addRight (-s)).toEmbedding
  have hE : E.card=4 := by simpa [E] using hD
  let e := cosetCoordinates hodd H r hgen
  let F := productHoles e E
  have hc : HasRainbowCycle ((E : Set G)ᶜ) := by
    by_cases hin : ∃ i, (F i).card=4
    · obtain ⟨i,hi⟩ := hin
      have hh := lift_shifted_cycle hodd H (by omega) (F i) (by omega) (i.val • r) (ih (F i) hi)
      have he := productHoles_image_eq e E i (hi.trans hE.symm)
      have hset : (fun x : H => (x : G)+i.val • r) '' (F i : Set H) = (E : Set G) := by
        rw [← he,Finset.coe_map]
        rfl
      rwa [hset] at hh
    · apply glue_deleted_fibers hodd H r hgen hq E hs (by omega)
      intro i
      have hb : (F i).card≤4 := (productHoles_card_le e E i).trans_eq hE
      have hn : (F i).card≠4 := fun he => hin ⟨i,he⟩
      change (F i).card≤3 ∧ 3≤Nat.card H-(F i).card
      omega
  exact undo_translation_cycle D s hc

end SunFourDeletion
