import SunThreeDeletion.Surgery

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion Equiv
open scoped Classical

variable {G : Type*} [AddCommGroup G] {A : Set G}

/-- Two separated short segments; all six vertices must be distinct. -/
theorem delete_separated (C : RainbowCycle A) (hp : C.next.IsCycle)
    (hsupp : ∀ z, C.next z ≠ z ↔ z ∈ A)
    (e : Fin 6 ↪ G)
    (h01 : C.next (e 0) = e 1) (h12 : C.next (e 1) = e 2)
    (h34 : C.next (e 3) = e 4) (h45 : C.next (e 4) = e 5)
    (hc0 : e 0 + e 2 = e 4 + e 5) (hc3 : e 3 + e 5 = e 1 + e 2) :
    HasRainbowCycle (A \ {e 1, e 4}) := by
  classical
  have hn {i j : Fin 6} (h : i ≠ j) : e i ≠ e j := e.injective.ne h
  have h10 := hn (by decide : (1 : Fin 6) ≠ 0)
  have h12n := hn (by decide : (1 : Fin 6) ≠ 2)
  have h14 := hn (by decide : (1 : Fin 6) ≠ 4)
  have h15 := hn (by decide : (1 : Fin 6) ≠ 5)
  have h20 := hn (by decide : (2 : Fin 6) ≠ 0)
  have h24 := hn (by decide : (2 : Fin 6) ≠ 4)
  have h25 := hn (by decide : (2 : Fin 6) ≠ 5)
  have h43 := hn (by decide : (4 : Fin 6) ≠ 3)
  have h45n := hn (by decide : (4 : Fin 6) ≠ 5)
  have h53 := hn (by decide : (5 : Fin 6) ≠ 3)
  let p := C.next
  let p1 := swap (e 1) (e 2) * p
  let q := swap (e 4) (e 5) * p1
  have hfirst : p1.IsCycle := by
    have h := hp.swap_mul (x := e 1) (by rw [h12]; exact h12n.symm) (by
      rw [h12]
      intro hh
      exact h20 (C.next.injective (hh.trans h01.symm)))
    simpa only [p1, h12] using h
  have hq14 : p1 (e 4) = e 5 := by
    simp [p1, p, h45, swap_apply_of_ne_of_ne h15.symm h25.symm]
  have hp51 : p (e 5) ≠ e 1 := fun h =>
    (hn (by decide : (5 : Fin 6) ≠ 0)) (p.injective (h.trans h01.symm))
  have hp52 : p (e 5) ≠ e 2 := fun h => h15.symm (p.injective (h.trans h12.symm))
  have hp54 : p (e 5) ≠ e 4 := fun h => h53 (p.injective (h.trans h34.symm))
  have hq15 : p1 (e 5) = p (e 5) := by simp [p1, swap_apply_of_ne_of_ne hp51 hp52]
  have hqcycle : q.IsCycle := by
    have h := hfirst.swap_mul (x := e 4) (by rw [hq14]; exact h45n.symm)
      (by rw [hq14, hq15]; exact hp54)
    simpa only [q, hq14] using h
  have hqapply (s : G) (hs1 : s ≠ e 1) (hs4 : s ≠ e 4) :
      q s = if s = e 0 then e 2 else if s = e 3 then e 5 else p s := by
    by_cases hs0 : s = e 0
    · subst s
      simp [q, p1, p, h01, swap_apply_of_ne_of_ne h24 h25]
    by_cases hs3 : s = e 3
    · subst s
      simp [q, p1, p, h34, hs0, swap_apply_of_ne_of_ne h14.symm h24.symm]
    have hh1 : p s ≠ e 1 := fun h => hs0 (p.injective (h.trans h01.symm))
    have hh2 : p s ≠ e 2 := fun h => hs1 (p.injective (h.trans h12.symm))
    have hh4 : p s ≠ e 4 := fun h => hs3 (p.injective (h.trans h34.symm))
    have hh5 : p s ≠ e 5 := fun h => hs4 (p.injective (h.trans h45.symm))
    simp [q, p1, hs0, hs3, swap_apply_of_ne_of_ne hh1 hh2, swap_apply_of_ne_of_ne hh4 hh5]
  have hmem (i j : Fin 6) (hij : i ≠ j) (h : C.next (e i) = e j) : e i ∈ A :=
    (hsupp _).mp (by rw [h]; exact (hn hij).symm)
  have hm0 := hmem 0 1 (by decide) h01
  have hm1 := hmem 1 2 (by decide) h12
  have hm3 := hmem 3 4 (by decide) h34
  have hm4 := hmem 4 5 (by decide) h45
  have hqset : {s : G | q s ≠ s} = A \ {e 1, e 4} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases hs1 : s = e 1
    · subst s
      simp [q, p1, p, h12, swap_apply_of_ne_of_ne h14 h15]
    by_cases hs4 : s = e 4
    · subst s
      simp [q, p1, p, h45, swap_apply_of_ne_of_ne h15.symm h25.symm]
    rw [hqapply s hs1 hs4]
    by_cases hs0 : s = e 0
    · subst s
      simp [hm0, hs1, hs4, h20]
    by_cases hs3 : s = e 3
    · subst s
      simp [hm3, hs1, hs4, hs0, h53]
    simpa only [if_neg hs0, if_neg hs3, hs1, hs4, or_self, not_false_eq_true, and_true]
      using hsupp s
  refine ⟨⟨q, hqset ▸ hqcycle.isCycleOn, ?_⟩⟩
  intro s hs t ht h
  have hs1 : s ≠ e 1 := fun he => hs.2 (by simp [he])
  have hs4 : s ≠ e 4 := fun he => hs.2 (by simp [he])
  have ht1 : t ≠ e 1 := fun he => ht.2 (by simp [he])
  have ht4 : t ≠ e 4 := fun he => ht.2 (by simp [he])
  change s + q s = t + q t at h
  rw [hqapply s hs1 hs4, hqapply t ht1 ht4] at h
  -- Every new color is assigned to one removed tail; other colors retain their old tail.
  let tail : G → G := fun z => if z = e 0 then e 4 else if z = e 3 then e 1 else z
  have htail (z : G) (hz : z ∈ A) :
      tail z ∈ A := by
    simp only [tail]
    split_ifs <;> assumption
  have hcolor (z : G) :
      z + (if z = e 0 then e 2 else if z = e 3 then e 5 else p z) =
      tail z + p (tail z) := by
    simp only [tail]
    split_ifs with h0 h3
    · subst z; simpa only [p, h45] using hc0
    · subst z; simpa only [p, h12] using hc3
    · rfl
  rw [hcolor s, hcolor t] at h
  have he := C.rainbow (htail s hs.1) (htail t ht.1) h
  dsimp [tail] at he
  split_ifs at he <;> first
    | exact he
    | exact (hs1 he).elim
    | exact (hs4 he).elim
    | exact (ht1 he.symm).elim
    | exact (ht4 he.symm).elim
    | exact (h14 he).elim
    | exact (h14 he.symm).elim
    | subst_vars; rfl

end SunThreeDeletion

