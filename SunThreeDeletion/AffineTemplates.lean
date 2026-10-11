import SunThreeDeletion.CyclicTemplates
import SunTwoDeletion.Map
import Mathlib.Algebra.Ring.AddAut

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

theorem affine_three_cycle {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    (f : G ≃+ K) (t : K) (a b c : G)
    (h : HasRainbowCycle ({a,b,c}ᶜ : Set G)) :
    HasRainbowCycle ({f a+t, f b+t, f c+t}ᶜ : Set K) := by
  obtain ⟨C⟩ := h
  let D := (C.map f.toAddMonoidHom f.injective).translate t
  have he : (fun x : K => x+t) '' (f '' ({a,b,c}ᶜ : Set G)) =
      ({f a+t, f b+t, f c+t}ᶜ : Set K) := by
    rw [Set.image_image]
    let e : G ≃ K := f.toEquiv.trans (Equiv.addRight t)
    change e '' ({a,b,c}ᶜ : Set G) = _
    rw [e.image_compl]
    simp [e]
  exact ⟨he ▸ D⟩

theorem cyclic_nat_delete_or_bad (m t : ℕ) (hodd : Odd m) (hm : 49 ≤ m)
    (ht : 0 < t) (hlt : t < m) (hnz : t ≠ m-2) :
    HasRainbowCycle ({0, (t : ZMod m), ((t+2 : ℕ) : ZMod m)}ᶜ : Set (ZMod m)) ∨
    ∃ s : ℤ, BadRepresentative s ∧ (m : ℤ) ∣ (2*(t : ℤ)-s) := by
  have hsplit : ∃ k, 12 ≤ k ∧ (m = 4*k+1 ∨ m = 4*k+3) := by
    refine ⟨m/4, by omega, ?_⟩
    obtain ⟨j, hj⟩ := hodd
    omega
  obtain ⟨k, hk, h | h⟩ := hsplit
  · subst m
    have h' := q1_delete_or_bad k t hk ht hlt (by omega)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h'
  · subst m
    have h' := q3_delete_or_bad k t hk ht hlt (by omega)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h'

/-- A failed normalized deletion forces one of ten explicit residues. -/
theorem cyclic_zmod_delete_or_bad (m : ℕ) (hodd : Odd m) (hm : 49 ≤ m)
    (t : ZMod m) (ht : t ≠ 0) (ht2 : t+2 ≠ 0) :
    HasRainbowCycle ({0, t, t+2}ᶜ : Set (ZMod m)) ∨
    ∃ s : ℤ, BadRepresentative s ∧ (s : ZMod m) = 2*t := by
  haveI : NeZero m := ⟨by omega⟩
  have htval : 0 < t.val := by
    by_contra h
    have hv : t.val = 0 := by omega
    have hc := ZMod.natCast_zmod_val t
    rw [hv, Nat.cast_zero] at hc
    exact ht hc.symm
  have hne : t.val ≠ m-2 := by
    intro h
    apply ht2
    have heq : t.val+2=m := by omega
    have hc := congrArg (fun z : ℕ => (z : ZMod m)) heq
    simpa only [Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_zmod_val, ZMod.natCast_self] using hc
  rcases cyclic_nat_delete_or_bad m t.val hodd hm htval t.val_lt hne with h | h
  · left
    simpa only [Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_zmod_val] using h
  · obtain ⟨s, hs, hd⟩ := h
    refine Or.inr ⟨s, hs, ?_⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr hd
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      ZMod.natCast_zmod_val, sub_eq_zero] at hc
    exact hc.symm

end SunThreeDeletion

