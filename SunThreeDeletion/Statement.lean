import SunTwoDeletion.Ordering

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

/-- The indexed cyclic-ordering contract, with last-to-first wraparound. -/
def ThreeDeletionOrdering (G : Type*) [AddCommGroup G] [Finite G] (a b c : G) : Prop :=
  ∃ (n : ℕ) (hn : 0 < n) (v : Fin n ↪ G),
    n = Nat.card G - 3 ∧ 2 < n ∧
    Set.range v = ({a, b, c}ᶜ : Set G) ∧
    Function.Injective (fun i => v i + v (cyclicSuccessor hn i))

theorem ordering_of_three_cycle {G : Type*} [AddCommGroup G] [Finite G]
    (hsize : 2 < Nat.card G - 3) (a b c : G)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcycle : HasRainbowCycle ({a, b, c}ᶜ : Set G)) :
    ThreeDeletionOrdering G a b c := by
  classical
  letI := Fintype.ofFinite G
  obtain ⟨C⟩ := hcycle
  let s : Finset G := ({a, b, c} : Finset G)ᶜ
  have hs : (s : Set G) = ({a, b, c}ᶜ : Set G) := by
    ext z
    simp [s, and_comm, and_left_comm, and_assoc]
  have hcard : s.card = Nat.card G - 3 := by
    simp [s, Finset.card_compl, hab, hac, hbc, Nat.card_eq_fintype_card]
    omega
  have hpos : 0 < s.card := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  let C' : RainbowCycle (s : Set G) := ⟨C.next, hs.symm ▸ C.cyclic, hs.symm ▸ C.rainbow⟩
  obtain ⟨hn, v, hv, hinj, _⟩ := cycle_as_ordering s C' u hu
  exact ⟨s.card, hn, v, hcard, by omega, hv.trans hs, hinj⟩

/-- In particular the final vertex contributes its sum with vertex zero. -/
theorem cyclicSuccessor_last {n : ℕ} (hn : 0 < n) :
    cyclicSuccessor hn ⟨n-1, by omega⟩ = ⟨0, hn⟩ := by
  apply Fin.ext
  rw [cyclicSuccessor_val]
  simp [Nat.sub_add_cancel hn]

end SunThreeDeletion

