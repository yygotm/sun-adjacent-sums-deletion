import SunFourDeletion.PlaneForms
import SunTwoDeletion.Subgroups

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

theorem two_distinct_maximal [Nontrivial G] (hn : ¬ IsAddCyclic G) :
    ∃ H L : AddSubgroup G, IsCoatom H ∧ IsCoatom L ∧ H≠L := by
  classical
  letI : Finite (AddSubgroup G) :=
    Finite.of_injective (fun H : AddSubgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨H,hH⟩ := IsCoatomic.exists_coatom (α := AddSubgroup G)
  obtain ⟨x,_,hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hH.ne_top)
  have hxproper : AddSubgroup.zmultiples x≠⊤ := by
    intro h
    exact hn (isAddCyclic_iff_exists_zmultiples_eq_top.mpr ⟨x,h⟩)
  obtain ⟨L,hL,hxL⟩ := (eq_top_or_exists_le_coatom (AddSubgroup.zmultiples x)).resolve_left hxproper
  refine ⟨H,L,hH,hL,?_⟩
  intro he
  exact hx (he.symm ▸ hxL (AddSubgroup.mem_zmultiples x))

theorem prime_quotient_hom (p : ℕ) [Fact p.Prime] (H : AddSubgroup G)
    (hc : Nat.card (G ⧸ H)=p) :
    ∃ f : G →+ ZMod p, Function.Surjective f ∧ f.ker=H := by
  haveI : IsAddCyclic (G ⧸ H) := isAddCyclic_of_prime_card hc
  let e : (G ⧸ H) ≃+ ZMod p := by
    have ee := (zmodAddCyclicAddEquiv (inferInstance : IsAddCyclic (G ⧸ H))).symm
    rwa [hc] at ee
  let f := e.toAddMonoidHom.comp (QuotientAddGroup.mk' H)
  refine ⟨f,e.surjective.comp (QuotientAddGroup.mk'_surjective H),?_⟩
  ext x
  change e (QuotientAddGroup.mk x)=0 ↔ x∈H
  rw [← e.map_zero]
  exact e.injective.eq_iff.trans (QuotientAddGroup.eq_zero_iff x)

theorem distinct_maximal_not_le (H L : AddSubgroup G)
    (hH : IsCoatom H) (hL : IsCoatom L) (hne : H≠L) : ¬H≤L := by
  intro hle
  exact hne ((hH.le_iff_eq hL.ne_top).mp hle).symm

/-- Two distinct index-three kernels provide a surjection to the elementary plane. -/
theorem plane_quotient_of_two_maximal (H L : AddSubgroup G)
    (hH : IsCoatom H) (hL : IsCoatom L) (hne : H≠L)
    (hcH : Nat.card (G ⧸ H)=3) (hcL : Nat.card (G ⧸ L)=3) :
    ∃ F : G →+ (ZMod 3 × ZMod 3), Function.Surjective F := by
  classical
  obtain ⟨f,hf,hfk⟩ := prime_quotient_hom 3 H hcH
  obtain ⟨g,hg,hgk⟩ := prime_quotient_hom 3 L hcL
  have hHL := distinct_maximal_not_le H L hH hL hne
  have hLH := distinct_maximal_not_le L H hL hH (Ne.symm hne)
  obtain ⟨x,hxH,hxL⟩ : ∃ x, x∈H ∧ x∉L := by
    by_contra h
    push_neg at h
    exact hHL h
  obtain ⟨y,hyL,hyH⟩ : ∃ y, y∈L ∧ y∉H := by
    by_contra h
    push_neg at h
    exact hLH h
  have hfx : f x=0 := by change x∈f.ker; rwa [hfk]
  have hgy : g y=0 := by change y∈g.ker; rwa [hgk]
  have hgx : g x≠0 := by intro he; apply hxL; rw [← hgk]; exact he
  have hfy : f y≠0 := by intro he; apply hyH; rw [← hfk]; exact he
  refine ⟨f.prod g,?_⟩
  rintro ⟨a,b⟩
  refine ⟨(a/(f y)).val • y + (b/(g x)).val • x,?_⟩
  apply Prod.ext
  · change f (_+_)=a
    rw [map_add,map_nsmul,map_nsmul,hfx,smul_zero,add_zero]
    rw [nsmul_eq_mul,ZMod.natCast_zmod_val]
    exact div_mul_cancel₀ a hfy
  · change g (_+_)=b
    rw [map_add,map_nsmul,map_nsmul,hgy,smul_zero,zero_add]
    rw [nsmul_eq_mul,ZMod.natCast_zmod_val]
    exact div_mul_cancel₀ b hgx

end SunFourDeletion
