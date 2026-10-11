import SunTwoDeletion.Paths
import Mathlib.Tactic

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

variable {G : Type*} [AddCommGroup G] {A : Set G}

def reverseCycle (C : RainbowCycle A) : RainbowCycle A where
  next := C.next⁻¹
  cyclic := C.cyclic.inv
  rainbow := by
    intro x hx y hy heq
    have hx' := C.cyclic.inv.1.mapsTo hx
    have hy' := C.cyclic.inv.1.mapsTo hy
    have hh : C.next⁻¹ x + C.next (C.next⁻¹ x) =
        C.next⁻¹ y + C.next (C.next⁻¹ y) := by
      simpa [add_comm] using heq
    have hi := C.rainbow hx' hy' hh
    exact C.next.symm.injective hi

theorem neighbours_distinct [Finite G] (C : RainbowCycle A)
    (hcard : 3 ≤ Nat.card A) (x : G) (hx : x ∈ A) :
    C.next⁻¹ x ≠ C.next x := by
  classical
  let s := A.toFinite.toFinset
  have hs : (s : Set G) = A := Set.Finite.coe_toFinset _
  have hsc : 3 ≤ s.card := by
    have hc : Nat.card (s : Set G) = s.card := by simp
    rw [hs] at hc
    omega
  have hcyc : C.next.IsCycleOn (s : Set G) := hs.symm ▸ C.cyclic
  have hx' : x ∈ s := hs.symm.subset hx
  intro heq
  have hp : (C.next ^ 2) x = x := by
    have h := congrArg C.next heq
    simpa [pow_two] using h.symm
  have hd : s.card ∣ 2 := (hcyc.pow_apply_eq hx').mp hp
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

/-- Reverse the cycle if necessary to avoid one forbidden predecessor.
This is the orientation repair needed when the quotient has order three. -/
theorem predecessor_avoiding [Finite G] (C : RainbowCycle A)
    (hcard : 3 ≤ Nat.card A) (x : G) (hx : x ∈ A) (forbidden : G) :
    ∃ D : RainbowCycle A, ∃ w ∈ A, D.next w = x ∧ w ≠ forbidden := by
  by_cases h : C.next⁻¹ x = forbidden
  · refine ⟨reverseCycle C, C.next x, C.cyclic.1.mapsTo hx, ?_, ?_⟩
    · exact C.next.symm_apply_apply x
    · intro heq
      exact neighbours_distinct C hcard x hx (h.trans heq.symm)
  · exact ⟨C, C.next⁻¹ x, C.cyclic.inv.1.mapsTo hx, C.next.apply_symm_apply x, h⟩

end SunThreeDeletion

