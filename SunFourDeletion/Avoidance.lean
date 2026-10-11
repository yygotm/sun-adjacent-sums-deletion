import Mathlib.Tactic

set_option autoImplicit false
namespace SunFourDeletion

/-- A union bound for arbitrary permutations; no independence of forbidden sets. -/
theorem exists_avoiding_permutations {H I : Type*} [Fintype H] [Fintype I]
    (D : I → Finset H) (p : I → Equiv.Perm H)
    (hsmall : (∑ i, (D i).card) < Fintype.card H) :
    ∃ u : H, ∀ i, p i u ∉ D i := by
  classical
  let B : Finset H := Finset.univ.biUnion (fun i => (D i).map (p i).symm.toEmbedding)
  have hB : B.card < Fintype.card H := by
    have hh : B.card ≤ ∑ i, ((D i).map (p i).symm.toEmbedding).card :=
      Finset.card_biUnion_le
    simp only [Finset.card_map] at hh
    omega
  obtain ⟨u,hu⟩ : ∃ u : H, u ∉ B := by
    by_contra hn
    push_neg at hn
    have he : B=Finset.univ := Finset.eq_univ_of_forall hn
    simp only [he, Finset.card_univ, lt_self_iff_false] at hB
  refine ⟨u,?_⟩
  intro i hi
  apply hu
  apply Finset.mem_biUnion.mpr
  refine ⟨i,Finset.mem_univ i,?_⟩
  apply Finset.mem_map.mpr
  exact ⟨p i u,hi,(p i).symm_apply_apply u⟩

end SunFourDeletion
