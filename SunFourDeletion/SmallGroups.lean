import SunFourDeletion.PlaneBase
import SunFourDeletion.PlaneFive
import SunFourDeletion.ThinFibers

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion SunThreeDeletion

theorem map_finset_cycle {K G : Type*} [AddCommGroup K] [AddCommGroup G]
    (e : K ≃+ G) (D : Finset K) (h : HasRainbowCycle ((D : Set K)ᶜ)) :
    HasRainbowCycle ((D.map e.toEmbedding : Set G)ᶜ) := by
  obtain ⟨C⟩ := h
  have hh := C.map e.toAddMonoidHom e.injective
  change RainbowCycle (e '' (D : Set K)ᶜ) at hh
  rw [Set.image_compl_eq e.bijective] at hh
  have he : e '' (D : Set K)=(D.map e.toEmbedding : Set G) := by
    ext x
    simp only [Set.mem_image,Finset.mem_coe,Finset.mem_map]
    rfl
  exact ⟨he ▸ hh⟩

theorem four_of_equiv {K G : Type*} [AddCommGroup K] [AddCommGroup G]
    (e : K ≃+ G)
    (h : ∀ E : Finset K, E.card=4 → HasRainbowCycle ((E : Set K)ᶜ))
    (D : Finset G) (hD : D.card=4) : HasRainbowCycle ((D : Set G)ᶜ) := by
  let E := D.map e.symm.toEmbedding
  have hE : E.card=4 := by simpa [E] using hD
  have hh := map_finset_cycle e E (h E hE)
  have he : E.map e.toEmbedding=D := by ext x; simp [E]
  rwa [he] at hh

theorem plane_five_cycle (D : Finset (ZMod 5 × ZMod 5)) (hD : D.card=4) :
    HasRainbowCycle ((D : Set (ZMod 5 × ZMod 5))ᶜ) := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨f,hf,hthin⟩ := five_direction D hD
  have hq : Nat.card ((ZMod 5 × ZMod 5) ⧸ f.ker)=5 := by
    have hh := Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv
    simpa using hh
  have hH : Nat.card f.ker=5 := by
    have hh := f.ker.card_eq_card_quotient_mul_card_addSubgroup
    simp only [Nat.card_prod,Nat.card_zmod,hq] at hh
    omega
  apply thin_hom_cycle (by norm_num [Nat.card_prod,Nat.card_zmod]) 5 (by decide) f hf
    (by omega) D hD hthin

theorem noncyclic_nine_four {G : Type*} [AddCommGroup G] [Finite G]
    (h9 : Nat.card G=9) (hn : ¬ IsAddCyclic G) (D : Finset G) (hD : D.card=4) :
    HasRainbowCycle ((D : Set G)ᶜ) := by
  obtain ⟨e⟩ := prime_square_equiv 3 (by simpa using h9) hn
  exact four_of_equiv e plane_four D hD

theorem noncyclic_twentyfive_four {G : Type*} [AddCommGroup G] [Finite G]
    (h25 : Nat.card G=25) (hn : ¬ IsAddCyclic G) (D : Finset G) (hD : D.card=4) :
    HasRainbowCycle ((D : Set G)ᶜ) := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨e⟩ := prime_square_equiv 5 (by simpa using h25) hn
  exact four_of_equiv e plane_five_cycle D hD

end SunFourDeletion
