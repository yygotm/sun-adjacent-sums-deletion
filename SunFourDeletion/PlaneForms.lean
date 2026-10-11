import SunFourDeletion.PrimeSquare

set_option autoImplicit false
namespace SunFourDeletion

def planeForm (p : ℕ) (j : Fin (p+1)) : (ZMod p × ZMod p) →+ ZMod p where
  toFun x := if j.val=p then x.2 else x.1+(j.val : ZMod p)*x.2
  map_zero' := by simp
  map_add' := by
    intro x y
    dsimp
    split_ifs <;> ring

theorem planeForm_surjective (p : ℕ) (j : Fin (p+1)) : Function.Surjective (planeForm p j) := by
  intro t
  by_cases hj : j.val=p
  · exact ⟨(0,t),by simp [planeForm,hj]⟩
  · exact ⟨(t,0),by simp [planeForm,hj]⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem three_plane_avoid (a b c : ZMod 3 × ZMod 3) :
    ∃ j : Fin 4, ∃ t : ZMod 3, t≠0 ∧
      t≠planeForm 3 j a ∧ t≠planeForm 3 j b ∧ t≠planeForm 3 j c := by
  have h : ∀ a b c : ZMod 3 × ZMod 3,
      ∃ j : Fin 4, ∃ t : ZMod 3, t≠0 ∧
        t≠planeForm 3 j a ∧ t≠planeForm 3 j b ∧ t≠planeForm 3 j c := by decide
  exact h a b c

end SunFourDeletion
