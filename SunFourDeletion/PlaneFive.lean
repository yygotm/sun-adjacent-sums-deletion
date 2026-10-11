import SunFourDeletion.PlaneForms
import SunFourDeletion.Transport

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace SunFourDeletion

theorem normalized_five_direction (a b c : ZMod 5 × ZMod 5)
    (hcard : ({0,a,b,c} : Finset (ZMod 5 × ZMod 5)).card=4) :
    ∃ j : Fin 6, ∀ t : ZMod 5,
      (({0,a,b,c} : Finset (ZMod 5 × ZMod 5)).filter
        (fun x => planeForm 5 j x=t)).card≤2 := by
  have h : ∀ a b c : ZMod 5 × ZMod 5,
      ({0,a,b,c} : Finset (ZMod 5 × ZMod 5)).card=4 →
      ∃ j : Fin 6, ∀ t : ZMod 5,
        (({0,a,b,c} : Finset (ZMod 5 × ZMod 5)).filter
          (fun x => planeForm 5 j x=t)).card≤2 := by decide
  exact h a b c hcard

theorem five_direction_zero (D : Finset (ZMod 5 × ZMod 5))
    (hD : D.card=4) (h0 : 0∈D) :
    ∃ j : Fin 6, ∀ t : ZMod 5, (D.filter (fun x => planeForm 5 j x=t)).card≤2 := by
  have he : (D.erase 0).card=3 := by rw [Finset.card_erase_of_mem h0,hD]
  obtain ⟨a,b,c,_,_,_,hc⟩ := Finset.card_eq_three.mp he
  have hd : D={0,a,b,c} := by rw [← Finset.insert_erase h0,hc]
  rw [hd]
  exact normalized_five_direction a b c (hd ▸ hD)

theorem five_direction (D : Finset (ZMod 5 × ZMod 5)) (hD : D.card=4) :
    ∃ f : (ZMod 5 × ZMod 5) →+ ZMod 5, Function.Surjective f ∧
      ∀ y : ZMod 5, (D.filter (fun x => f x=y)).card≤2 := by
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0<D.card)
  let E := D.map (Equiv.addRight (-a)).toEmbedding
  have hE : E.card=4 := by simpa [E] using hD
  have h0 : 0∈E := Finset.mem_map.mpr ⟨a,ha,by simp⟩
  obtain ⟨j,hj⟩ := five_direction_zero E hE h0
  refine ⟨planeForm 5 j,planeForm_surjective 5 j,?_⟩
  intro y
  have hh := hj (y+planeForm 5 j (-a))
  rw [translate_filter_card] at hh
  simpa using hh

end SunFourDeletion
