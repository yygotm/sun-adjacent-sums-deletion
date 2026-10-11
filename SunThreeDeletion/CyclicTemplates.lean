import SunThreeDeletion.QSpecial
import SunThreeDeletion.QDelete

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

theorem q1_special_cycle (k : ℕ) (hk : 12 ≤ k) :
    HasRainbowCycle ({0, ((4*k : ℕ) : ZMod (4*k+1)), 1}ᶜ : Set (ZMod (4*k+1))) := by
  obtain ⟨C, _, hzero, hn⟩ := q1_cycle k (by omega)
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := q1_special_values k hk
  have step (i a b : ℕ) (hi : i+1<4*k) (ha : q1Vertex k i = a)
      (hb : q1Vertex k (i+1) = b) : C.next (a : ZMod (4*k+1)) = (b : ZMod (4*k+1)) := by
    simpa only [if_pos hi, ha, hb] using hn ⟨i, by omega⟩
  have hA : 4*k+1-3 = 4*k-2 := by omega
  have hB : 4*k+1-1 = 4*k := by omega
  have hD : 4*k+1-2 = 4*k-1 := by omega
  have h := special_deletion (4*k+1) (by omega) C hzero
    (by rw [hA, hB]; exact step (k-2) _ _ (by omega) h0 (by convert h1 using 2 <;> omega))
    (by rw [hB]; exact step (k-1) _ _ (by omega) h1 (by convert h2 using 2 <;> omega))
    (step (3*k-2) _ _ (by omega) h3 (by convert h4 using 2 <;> omega))
    (by rw [hD]; exact step (3*k-1) _ _ (by omega) h4 (by convert h5 using 2 <;> omega))
  simpa only [hB] using h

theorem q3_special_cycle (k : ℕ) (hk : 12 ≤ k) :
    HasRainbowCycle ({0, ((4*k+2 : ℕ) : ZMod (4*k+3)), 1}ᶜ : Set (ZMod (4*k+3))) := by
  obtain ⟨C, _, hzero, hn⟩ := q3_cycle k (by omega)
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := q3_special_values k hk
  have step (i a b : ℕ) (hi : i+1<4*k+2) (ha : q3Vertex k i = a)
      (hb : q3Vertex k (i+1) = b) : C.next (a : ZMod (4*k+3)) = (b : ZMod (4*k+3)) := by
    simpa only [if_pos hi, ha, hb] using hn ⟨i, by omega⟩
  have hA : 4*k+3-3 = 4*k := by omega
  have hB : 4*k+3-1 = 4*k+2 := by omega
  have hD : 4*k+3-2 = 4*k+1 := by omega
  have h := special_deletion (4*k+3) (by omega) C hzero
    (by rw [hA, hB]; exact step (k-1) _ _ (by omega) h0 (by convert h1 using 2 <;> omega))
    (by rw [hB]; exact step k _ _ (by omega) h1 h2)
    (step (3*k) _ _ (by omega) h3 h4)
    (by rw [hD]; exact step (3*k+1) _ _ (by omega) h4 (by convert h5 using 2 <;> omega))
  simpa only [hB] using h

theorem q1_delete_or_bad (k t : ℕ) (hk : 12 ≤ k)
    (ht : 0 < t) (hlt : t < 4*k+1) (hnz : t ≠ 4*k-1) :
    HasRainbowCycle ({0, (t : ZMod (4*k+1)), ((t+2 : ℕ) : ZMod (4*k+1))}ᶜ :
      Set (ZMod (4*k+1))) ∨
    ∃ s : ℤ, BadRepresentative s ∧ (4*(k : ℤ)+1) ∣ (2*(t : ℤ)-s) := by
  by_cases hi : Interior1 k t
  · left
    obtain ⟨C, _, hzero, hn⟩ := q1_cycle k (by omega)
    exact delete_four_run (4*k) t (q1Vertex k)
      (fun i hi => q1Vertex_bounds k i (by omega) hi) (q1Vertex_injective k (by omega))
      C hzero hn (interior1_four_run k t hk hi)
  by_cases he : t = 4*k
  · left
    subst t
    have hc : ((4*k+2 : ℕ) : ZMod (4*k+1)) = 1 := by
      have hn : 4*k+2 = (4*k+1)+1 := by omega
      rw [hn, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
    rw [hc]
    exact q1_special_cycle k hk
  · exact Or.inr (boundary1_small_double k t hk (boundary1_of_not_interior k t hk ht hlt hnz hi) he)

theorem q3_delete_or_bad (k t : ℕ) (hk : 12 ≤ k)
    (ht : 0 < t) (hlt : t < 4*k+3) (hnz : t ≠ 4*k+1) :
    HasRainbowCycle ({0, (t : ZMod (4*k+3)), ((t+2 : ℕ) : ZMod (4*k+3))}ᶜ :
      Set (ZMod (4*k+3))) ∨
    ∃ s : ℤ, BadRepresentative s ∧ (4*(k : ℤ)+3) ∣ (2*(t : ℤ)-s) := by
  by_cases hi : Interior3 k t
  · left
    obtain ⟨C, _, hzero, hn⟩ := q3_cycle k (by omega)
    exact delete_four_run (4*k+2) t (q3Vertex k)
      (fun i hi => q3Vertex_bounds k i (by omega) hi) (q3Vertex_injective k (by omega))
      C hzero hn (interior3_four_run k t hk hi)
  by_cases he : t = 4*k+2
  · left
    subst t
    have hc : ((4*k+2+2 : ℕ) : ZMod (4*k+3)) = 1 := by
      have hn : 4*k+2+2 = (4*k+3)+1 := by omega
      rw [hn, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
    rw [hc]
    exact q3_special_cycle k hk
  · exact Or.inr (boundary3_small_double k t hk (boundary3_of_not_interior k t hk ht hlt hnz hi) he)

end SunThreeDeletion

