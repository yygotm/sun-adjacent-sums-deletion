import Mathlib.Tactic

set_option autoImplicit false
namespace SunFourDeletion

variable {I H G : Type*} [Fintype I] [Fintype H]

noncomputable def productHoles (e : I × H ≃ G) (D : Finset G) (i : I) : Finset H := by
  classical
  exact Finset.univ.filter (fun h => e (i,h)∈D)

@[simp] theorem mem_productHoles (e : I × H ≃ G) (D : Finset G) (i : I) (h : H) :
    h∈productHoles e D i ↔ e (i,h)∈D := by
  classical
  simp [productHoles]

def fiberEmbedding (e : I × H ≃ G) (i : I) : H ↪ G :=
  ⟨fun h => e (i,h),fun _ _ he => (Prod.mk.inj (e.injective he)).2⟩

theorem sum_productHoles_card (e : I × H ≃ G) (D : Finset G) :
    (∑ i, (productHoles e D i).card)=D.card := by
  classical
  have hc : (Finset.univ.sigma (productHoles e D)).card=D.card := by
    apply Finset.card_bij (fun p _ => e (p.1,p.2))
    · intro p hp
      exact (mem_productHoles e D p.1 p.2).mp (Finset.mem_sigma.mp hp).2
    · intro p hp t ht he
      have hh := e.injective he
      rcases p with ⟨i,x⟩
      rcases t with ⟨j,y⟩
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hh
      rfl
    · intro x hx
      refine ⟨⟨(e.symm x).1,(e.symm x).2⟩,?_,?_⟩
      · apply Finset.mem_sigma.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        rw [mem_productHoles]
        simpa only [Prod.mk.eta,e.apply_symm_apply] using hx
      · simp
  simpa only [Finset.card_sigma] using hc

theorem productHoles_image_subset (e : I × H ≃ G) (D : Finset G) (i : I) :
    (productHoles e D i).map (fiberEmbedding e i) ⊆ D := by
  intro x hx
  obtain ⟨h,hh,rfl⟩ := Finset.mem_map.mp hx
  exact (mem_productHoles e D i h).mp hh

theorem productHoles_card_le (e : I × H ≃ G) (D : Finset G) (i : I) :
    (productHoles e D i).card≤D.card := by
  have hh := Finset.card_le_card (productHoles_image_subset e D i)
  simpa only [Finset.card_map] using hh

theorem productHoles_image_eq (e : I × H ≃ G) (D : Finset G) (i : I)
    (hc : (productHoles e D i).card=D.card) :
    (productHoles e D i).map (fiberEmbedding e i)=D := by
  apply Finset.eq_of_subset_of_card_le (productHoles_image_subset e D i)
  rw [Finset.card_map,hc]

theorem retained_fiber_union (e : I × H ≃ G) (D : Finset G) :
    (⋃ i, (fun h => e (i,h)) '' ((productHoles e D i : Set H)ᶜ)) = (D : Set G)ᶜ := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,h,hh,rfl⟩ := Set.mem_iUnion.mp hx
    exact fun hd => hh ((mem_productHoles e D i h).mpr hd)
  · intro hx
    apply Set.mem_iUnion.mpr
    refine ⟨(e.symm x).1,(e.symm x).2,?_,by simp⟩
    intro hh
    apply hx
    have hd := (mem_productHoles e D (e.symm x).1 (e.symm x).2).mp hh
    simpa using hd

end SunFourDeletion
