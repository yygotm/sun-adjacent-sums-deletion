import SunThreeDeletion.Certificate

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion Equiv
open scoped Classical

variable {G : Type*} [AddCommGroup G] {A : Set G}

noncomputable def skipAdjacent (p : Perm G) (x y v : G) : Perm G := by
  classical
  exact swap y v * (swap x y * p)

theorem skipAdjacent_apply (p : Perm G) (u x y v z : G)
    (hpu : p u = x) (hpx : p x = y) (hpy : p y = v)
    (hxy : x ≠ y) (hxv : x ≠ v) (hyv : y ≠ v)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    skipAdjacent p x y v z = if z = u then v else p z := by
  classical
  by_cases hzu : z = u
  · subst z
    simp [skipAdjacent, hpu]
  · have h0 : p z ≠ x := fun h => hzu (p.injective (h.trans hpu.symm))
    have h1 : p z ≠ y := fun h => hzx (p.injective (h.trans hpx.symm))
    have h2 : p z ≠ v := fun h => hzy (p.injective (h.trans hpy.symm))
    simp [skipAdjacent, hzu, swap_apply_of_ne_of_ne h0 h1,
      swap_apply_of_ne_of_ne h1 h2]

/-- Remove the middle two vertices of a four-vertex segment, reusing its middle color. -/
theorem delete_adjacent (C : RainbowCycle A) (hp : C.next.IsCycle)
    (hsupp : ∀ z, C.next z ≠ z ↔ z ∈ A)
    (u x y v : G) (hpu : C.next u = x) (hpx : C.next x = y) (hpy : C.next y = v)
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (hxy : x ≠ y) (hxv : x ≠ v) (hyv : y ≠ v)
    (hsum : u + v = x + y) :
    HasRainbowCycle (A \ {x, y}) := by
  classical
  let p := C.next
  let q := skipAdjacent p x y v
  have hfirst : (swap x y * p).IsCycle := by
    have h := hp.swap_mul (x := x) (by rw [hpx]; exact hxy.symm)
      (by rw [hpx, hpy]; exact hxv.symm)
    simpa only [hpx] using h
  have hfy : (swap x y * p) y = v := by
    simp [p, hpy, swap_apply_of_ne_of_ne hxv.symm hyv.symm]
  have hpvx : p v ≠ x := fun h => huv (p.injective (hpu.trans h.symm))
  have hpvy : p v ≠ y := fun h => hxv (p.injective (hpx.trans h.symm))
  have hfv : (swap x y * p) v = p v := by
    simp [swap_apply_of_ne_of_ne hpvx hpvy]
  have hqcycle : q.IsCycle := by
    have h := hfirst.swap_mul (x := y) (by rw [hfy]; exact hyv.symm)
      (by rw [hfy, hfv]; exact hpvy)
    simpa only [hfy, q, skipAdjacent] using h
  have hqapply (z : G) (hzx : z ≠ x) (hzy : z ≠ y) :
      q z = if z = u then v else p z :=
    skipAdjacent_apply p u x y v z hpu hpx hpy hxy hxv hyv hzx hzy
  have hqset : {z : G | q z ≠ z} = A \ {x, y} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases hzx : z = x
    · subst z
      simp [q, skipAdjacent, p, hpx, swap_apply_of_ne_of_ne hxy hxv]
    by_cases hzy : z = y
    · subst z
      simp [q, skipAdjacent, p, hpy, swap_apply_of_ne_of_ne hxv.symm hyv.symm]
    rw [hqapply z hzx hzy]
    by_cases hzu : z = u
    · subst z
      have huA : u ∈ A := (hsupp u).mp (by rw [hpu]; exact hux.symm)
      simp [huA, huv.symm, hux, huy]
    · simpa only [if_neg hzu, hzx, hzy, or_self, not_false_eq_true, and_true] using hsupp z
  refine ⟨⟨q, hqset ▸ hqcycle.isCycleOn, ?_⟩⟩
  intro z hz w hw h
  have hzx : z ≠ x := fun he => hz.2 (by simp [he])
  have hzy : z ≠ y := fun he => hz.2 (by simp [he])
  have hwx : w ≠ x := fun he => hw.2 (by simp [he])
  have hwy : w ≠ y := fun he => hw.2 (by simp [he])
  change z + q z = w + q w at h
  rw [hqapply z hzx hzy, hqapply w hwx hwy] at h
  have hxA : x ∈ A := (hsupp x).mp (by rw [hpx]; exact hxy.symm)
  split_ifs at h with hzu hwu hwu
  · exact hzu.trans hwu.symm
  · subst z
    have he : x + C.next x = w + C.next w := by rw [hpx]; exact hsum.symm.trans h
    exact (hwx (C.rainbow hxA hw.1 he).symm).elim
  · subst w
    have he : z + C.next z = x + C.next x := by rw [hpx]; exact h.trans hsum
    exact (hzx (C.rainbow hz.1 hxA he)).elim
  · exact C.rainbow hz.1 hw.1 h

end SunThreeDeletion

