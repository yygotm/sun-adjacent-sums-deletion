import SunThreeDeletion.QArithmetic
import SunThreeDeletion.Certificate

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

theorem natCast_injective_of_bounds {m n : ℕ} (f : Fin n → ℕ)
    (hb : ∀ i, f i < m) (hf : Function.Injective f) :
    Function.Injective (fun i => (f i : ZMod m)) := by
  intro i j h
  apply hf
  have hval := congrArg ZMod.val h
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (hb i),
    Nat.mod_eq_of_lt (hb j)] using hval

theorem range_natCast_nonzero {n : ℕ} (f : Fin n → ℕ)
    (hb : ∀ i, 0 < f i ∧ f i < n+1) (hf : Function.Injective f) :
    Set.range (fun i => (f i : ZMod (n+1))) = ({0}ᶜ : Set (ZMod (n+1))) := by
  let g : Fin n → Fin n := fun i => ⟨f i-1, by have := hb i; omega⟩
  have hg : Function.Injective g := by
    intro i j h
    apply hf
    have hval := congrArg Fin.val h
    have hi := (hb i).1
    have hj := (hb j).1
    change f i-1 = f j-1 at hval
    omega
  have hsurj := Finite.surjective_of_injective hg
  ext z
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩ heq
    have hv := congrArg ZMod.val heq
    have hpos := (hb i).1
    rw [ZMod.val_natCast_of_lt (hb i).2] at hv
    simp only [ZMod.val_zero] at hv
    omega
  · intro hz
    have hpos : 0 < z.val := by
      have hne : z.val ≠ 0 := by
        intro heq
        have hc := ZMod.natCast_zmod_val z
        rw [heq, Nat.cast_zero] at hc
        exact hz hc.symm
      omega
    have hlt := z.val_lt
    obtain ⟨i, hi⟩ := hsurj ⟨z.val-1, by omega⟩
    have hval := congrArg Fin.val hi
    have hib := hb i
    have heq : f i = z.val := by change f i-1 = z.val-1 at hval; omega
    exact ⟨i, by rw [heq, ZMod.natCast_zmod_val]⟩

theorem rotate_val {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (finRotate n i).val = if i.val+1 < n then i.val+1 else 0 := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [coe_finRotate]
  split_ifs <;> simp_all only [Fin.ext_iff, Fin.val_last] <;> omega

/-- A reusable conversion from natural representatives and complete edge-sum data. -/
theorem one_hole_of_arithmetic {n : ℕ} (hn : 2 ≤ n)
    (v c : ℕ → ℕ)
    (hv : ∀ i, i < n → 0 < v i ∧ v i < n+1)
    (hc : ∀ i, i < n → 0 < c i ∧ c i < n+1)
    (hvi : Function.Injective (fun i : Fin n => v i.val))
    (hci : Function.Injective (fun i : Fin n => c i.val))
    (hs : ∀ i, i < n →
      v i + v (if i+1<n then i+1 else 0) = c i ∨
      v i + v (if i+1<n then i+1 else 0) = c i+(n+1)) :
    ∃ C : RainbowCycle ({0}ᶜ : Set (ZMod (n+1))),
      C.colors = ({0}ᶜ : Set (ZMod (n+1))) ∧ C.next 0 = 0 ∧
      ∀ i : Fin n, C.next (v i.val : ZMod (n+1)) =
        (v (if i.val+1<n then i.val+1 else 0) : ZMod (n+1)) := by
  let e : Fin n ↪ ZMod (n+1) :=
    ⟨fun i => (v i.val : ZMod (n+1)),
      natCast_injective_of_bounds _ (fun i => (hv i.val i.isLt).2) hvi⟩
  have he : Set.range e = ({0}ᶜ : Set (ZMod (n+1))) :=
    range_natCast_nonzero _ (fun i => hv i.val i.isLt) hvi
  have hsum (i : Fin n) : e i + e (finRotate n i) = (c i.val : ZMod (n+1)) := by
    change (v i.val : ZMod (n+1)) + (v (finRotate n i).val : ZMod (n+1)) = _
    rw [rotate_val (by omega), ← Nat.cast_add]
    rcases hs i.val i.isLt with h | h
    · rw [h]
    · rw [h, Nat.cast_add, ZMod.natCast_self, add_zero]
  have hinj : Function.Injective (fun i => e i + e (finRotate n i)) := by
    simp_rw [hsum]
    exact natCast_injective_of_bounds _ (fun i => (hc i.val i.isLt).2) hci
  let C := RainbowCycle.ofEmbedding (finRotate n) (finRotate_isCycleOn hn) e hinj
  have hcolors : C.colors = ({0}ᶜ : Set (ZMod (n+1))) := by
    rw [RainbowCycle.ofEmbedding_colors]
    simp_rw [hsum]
    exact range_natCast_nonzero _ (fun i => hc i.val i.isLt) hci
  let C' : RainbowCycle ({0}ᶜ : Set (ZMod (n+1))) :=
    ⟨C.next, he ▸ C.cyclic, he ▸ C.rainbow⟩
  have hec : C'.colors = C.colors :=
    congrArg (fun A : Set (ZMod (n+1)) => (fun x => x + C.next x) '' A) he.symm
  refine ⟨C', hec.trans hcolors, ?_, ?_⟩
  · change (finRotate n).viaEmbedding e 0 = 0
    apply Equiv.Perm.viaEmbedding_apply_of_notMem
    rw [he]
    simp
  · intro i
    change C.next (e i) = _
    rw [RainbowCycle.ofEmbedding_next]
    change (v (finRotate n i).val : ZMod (n+1)) = _
    rw [rotate_val (by omega)]

theorem q1_cycle (k : ℕ) (hk : 0 < k) :
    ∃ C : RainbowCycle ({0}ᶜ : Set (ZMod (4*k+1))),
      C.colors = ({0}ᶜ : Set (ZMod (4*k+1))) ∧ C.next 0 = 0 ∧
      ∀ i : Fin (4*k), C.next (q1Vertex k i.val : ZMod (4*k+1)) =
        (q1Vertex k (if i.val+1<4*k then i.val+1 else 0) : ZMod (4*k+1)) :=
  one_hole_of_arithmetic (by omega) (q1Vertex k) (q1Color k)
    (fun i hi => q1Vertex_bounds k i hk hi) (fun i hi => q1Color_bounds k i hk hi)
    (q1Vertex_injective k hk) (q1Color_injective k hk) (fun i hi => q1_sum k i hk hi)

theorem q3_cycle (k : ℕ) (hk : 0 < k) :
    ∃ C : RainbowCycle ({0}ᶜ : Set (ZMod (4*k+3))),
      C.colors = ({0}ᶜ : Set (ZMod (4*k+3))) ∧ C.next 0 = 0 ∧
      ∀ i : Fin (4*k+2), C.next (q3Vertex k i.val : ZMod (4*k+3)) =
        (q3Vertex k (if i.val+1<4*k+2 then i.val+1 else 0) : ZMod (4*k+3)) :=
  one_hole_of_arithmetic (by omega) (q3Vertex k) (q3Color k)
    (fun i hi => q3Vertex_bounds k i hk hi) (fun i hi => q3Color_bounds k i hk hi)
    (q3Vertex_injective k hk) (q3Color_injective k hk) (fun i hi => q3_sum k i hk hi)

/-- The one-hole harmonious cycle is proved directly, without a literature axiom. -/
theorem cyclic_one_deletion (m : ℕ) (hodd : Odd m) (hm : 5 ≤ m) :
    ∃ C : RainbowCycle ({0}ᶜ : Set (ZMod m)), C.colors = ({0}ᶜ : Set (ZMod m)) := by
  have hcases : m = 4*(m/4)+1 ∨ m = 4*(m/4)+3 := by
    obtain ⟨s, hs⟩ := hodd
    omega
  rcases hcases with h | h
  · obtain ⟨C, hc, _⟩ := q1_cycle (m/4) (by omega)
    have hh : ∃ C : RainbowCycle ({0}ᶜ : Set (ZMod (4*(m/4)+1))),
        C.colors = ({0}ᶜ : Set (ZMod (4*(m/4)+1))) := ⟨C, hc⟩
    exact h.symm ▸ hh
  · obtain ⟨C, hc, _⟩ := q3_cycle (m/4) (by omega)
    have hh : ∃ C : RainbowCycle ({0}ᶜ : Set (ZMod (4*(m/4)+3))),
        C.colors = ({0}ᶜ : Set (ZMod (4*(m/4)+3))) := ⟨C, hc⟩
    exact h.symm ▸ hh

end SunThreeDeletion

