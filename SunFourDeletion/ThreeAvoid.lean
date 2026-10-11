import SunFourDeletion.MaximalQuotients

set_option autoImplicit false
namespace SunFourDeletion

theorem three_four_images_avoid (a b c d : ZMod 3 × ZMod 3) :
    ∃ j : Fin 4, ∃ t : ZMod 3,
      planeForm 3 j a≠t ∧ planeForm 3 j b≠t ∧
      planeForm 3 j c≠t ∧ planeForm 3 j d≠t := by
  obtain ⟨j,t,ht0,htb,htc,htd⟩ := three_plane_avoid (b-a) (c-a) (d-a)
  refine ⟨j,planeForm 3 j a+t,?_,?_,?_,?_⟩
  · intro h
    apply ht0
    exact (add_eq_left.mp h.symm)
  · intro h
    apply htb
    rw [map_sub,h]
    abel
  · intro h
    apply htc
    rw [map_sub,h]
    abel
  · intro h
    apply htd
    rw [map_sub,h]
    abel

theorem three_hom_avoids_four {G : Type*} [AddCommGroup G]
    (F : G →+ (ZMod 3 × ZMod 3)) (hF : Function.Surjective F)
    (D : Finset G) (hD : D.card=4) :
    ∃ f : G →+ ZMod 3, Function.Surjective f ∧ ∃ t : ZMod 3, ∀ d∈D, f d≠t := by
  classical
  obtain ⟨a,b,c,d,_,_,_,_,_,_,rfl⟩ := Finset.card_eq_four.mp hD
  obtain ⟨j,t,ha,hb,hc,hd⟩ := three_four_images_avoid (F a) (F b) (F c) (F d)
  refine ⟨(planeForm 3 j).comp F,(planeForm_surjective 3 j).comp hF,t,?_⟩
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc
  · exact hd

end SunFourDeletion
