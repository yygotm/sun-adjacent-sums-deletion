import SunThreeDeletion.QCycle
import SunThreeDeletion.QInterior
import SunThreeDeletion.Surgery

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion Equiv

theorem delete_four_run (n t : ℕ) (f : ℕ → ℕ)
    (hf : ∀ i, i<n → 0 < f i ∧ f i < n+1)
    (hfi : Function.Injective (fun i : Fin n => f i.val))
    (C : RainbowCycle ({0}ᶜ : Set (ZMod (n+1)))) (hzero : C.next 0 = 0)
    (hnext : ∀ i : Fin n, C.next (f i.val : ZMod (n+1)) =
      (f (if i.val+1<n then i.val+1 else 0) : ZMod (n+1)))
    (hrun : FourRun f n t) :
    HasRainbowCycle ({0, (t : ZMod (n+1)), ((t+2 : ℕ) : ZMod (n+1))}ᶜ : Set (ZMod (n+1))) := by
  obtain ⟨j, hj, hmid, hsum⟩ := hrun
  have hinj := natCast_injective_of_bounds (fun i : Fin n => f i.val)
    (fun i => (hf i.val i.isLt).2) hfi
  have hne (s r : ℕ) (hs : s<n) (hr : r<n) (hne : s ≠ r) :
      (f s : ZMod (n+1)) ≠ (f r : ZMod (n+1)) := by
    intro h
    have hh := hinj (a₁ := ⟨s, hs⟩) (a₂ := ⟨r, hr⟩) h
    exact hne (congrArg Fin.val hh)
  have hmem (s : ℕ) (hs : s<n) : (f s : ZMod (n+1)) ∈ ({0}ᶜ : Set (ZMod (n+1))) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hz
    have h := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (hf s hs).2, ZMod.val_zero] at h
    have := (hf s hs).1
    omega
  have hnontriv : ({0}ᶜ : Set (ZMod (n+1))).Nontrivial :=
    ⟨f j, hmem j (by omega), f (j+1), hmem (j+1) (by omega),
      hne j (j+1) (by omega) (by omega) (by omega)⟩
  have hsupp (z : ZMod (n+1)) :
      C.next z ≠ z ↔ z ∈ ({0}ᶜ : Set (ZMod (n+1))) := by
    by_cases hz : z = 0
    · simp [hz, hzero]
    · have hzm : z ∈ ({0}ᶜ : Set (ZMod (n+1))) := by simpa using hz
      exact iff_of_true (C.cyclic.apply_ne hnontriv hzm) hzm
  have hp : C.next.IsCycle :=
    Equiv.Perm.isCycle_iff_exists_isCycleOn.mpr
      ⟨_, hnontriv, C.cyclic, fun z hz => (hsupp z).mp hz⟩
  have hsucc (s : ℕ) (hs : s+1<n) :
      C.next (f s : ZMod (n+1)) = (f (s+1) : ZMod (n+1)) := by
    simpa only [if_pos hs] using hnext ⟨s, by omega⟩
  have h := delete_adjacent C hp hsupp
    (f j) (f (j+1)) (f (j+2)) (f (j+3))
    (hsucc j (by omega)) (by convert hsucc (j+1) (by omega) using 1)
    (by convert hsucc (j+2) (by omega) using 1)
    (hne j (j+1) (by omega) (by omega) (by omega))
    (hne j (j+2) (by omega) (by omega) (by omega))
    (hne j (j+3) (by omega) (by omega) (by omega))
    (hne (j+1) (j+2) (by omega) (by omega) (by omega))
    (hne (j+1) (j+3) (by omega) (by omega) (by omega))
    (hne (j+2) (j+3) (by omega) (by omega) (by omega))
    (by simpa only [Nat.cast_add] using congrArg (fun z : ℕ => (z : ZMod (n+1))) hsum)
  have hset :
      ({0}ᶜ : Set (ZMod (n+1))) \ {(f (j+1) : ZMod (n+1)), (f (j+2) : ZMod (n+1))} =
      ({0, (t : ZMod (n+1)), ((t+2 : ℕ) : ZMod (n+1))}ᶜ : Set (ZMod (n+1))) := by
    rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      ext z <;> simp [h1, h2, and_comm, and_left_comm]
  rwa [hset] at h

end SunThreeDeletion

