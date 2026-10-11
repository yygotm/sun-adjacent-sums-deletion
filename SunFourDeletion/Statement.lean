import SunThreeDeletion.Statement

set_option autoImplicit false
namespace SunFourDeletion
open SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

/-- Coverage, no repeated vertices, and all cyclic sums, including the closing edge. -/
def RainbowEnumeration {n : ℕ} (hn : 0 < n) (A : Set G) (v : Fin n → G) : Prop :=
  Function.Injective v ∧ Set.range v = A ∧
    Function.Injective (fun i => v i + v (cyclicSuccessor hn i))

theorem ordering_of_four_cycle (hsize : 7 ≤ Nat.card G) (D : Finset G)
    (hD : D.card = 4) (hc : HasRainbowCycle ((D : Set G)ᶜ)) :
    ∃ (n : ℕ) (hn : 0 < n) (v : Fin n ↪ G),
      n = Nat.card G - 4 ∧ 2 < n ∧ Set.range v = (D : Set G)ᶜ ∧
      Function.Injective (fun i => v i + v (cyclicSuccessor hn i)) := by
  classical
  letI := Fintype.ofFinite G
  obtain ⟨C⟩ := hc
  let s : Finset G := Dᶜ
  have hs : (s : Set G) = (D : Set G)ᶜ := by simp [s]
  have hcard : s.card = Nat.card G - 4 := by
    simp [s, Finset.card_compl, hD, Nat.card_eq_fintype_card]
  have hpos : 0 < s.card := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  let C' : RainbowCycle (s : Set G) := ⟨C.next, hs.symm ▸ C.cyclic, hs.symm ▸ C.rainbow⟩
  obtain ⟨hn,v,hv,hi,_⟩ := cycle_as_ordering s C' u hu
  exact ⟨s.card,hn,v,hcard,by omega,hv.trans hs,hi⟩

theorem four_finset_card [DecidableEq G] (a b c d : G)
    (hab : a≠b) (hac : a≠c) (had : a≠d)
    (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    ({a,b,c,d} : Finset G).card = 4 := by
  classical
  simp [hab,hac,had,hbc,hbd,hcd]

end SunFourDeletion
