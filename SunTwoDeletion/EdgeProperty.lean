import SunTwoDeletion.GlueControl
import SunTwoDeletion.Rows
import SunTwoDeletion.Map

set_option autoImplicit false

namespace SunTwoDeletion

universe u

theorem three_le_of_odd_nontrivial (G : Type*) [AddCommGroup G] [Finite G]
    [Nontrivial G] (hodd : Odd (Nat.card G)) : 3 ≤ Nat.card G := by
  have h := Finite.one_lt_card (α := G)
  obtain ⟨k, hk⟩ := hodd
  omega

/-- Strong induction on the order of the ambient group. All recursive uses are
on a proper subgroup; the gluing and row lemmas make no call back to this theorem. -/
theorem edge_property_odd (G : Type u) [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) : EdgeProperty G := by
  suffices h : ∀ n, ∀ (K : Type u) [AddCommGroup K] [Finite K],
      Nat.card K = n → Odd n → EdgeProperty K from
    h (Nat.card G) G rfl hodd
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K _ _ hcard ho
    have hoddK : Odd (Nat.card K) := hcard.symm ▸ ho
    apply edge_property_of_zero
    intro d hd
    letI : Nontrivial K := nontrivial_of_ne d 0 hd
    obtain ⟨H, hproper, hp, hlt⟩ := exists_prime_quotient (G := K)
    have hE : EdgeProperty H :=
      ih (Nat.card H) (by omega) H rfl (subgroup_odd hoddK H)
    letI : Fact (Nat.card (K ⧸ H)).Prime := ⟨hp⟩
    haveI : IsAddCyclic (K ⧸ H) := isAddCyclic_of_prime_card rfl
    have hq : 3 ≤ Nat.card (K ⧸ H) := by
      have h2 := hp.one_lt
      obtain ⟨k, hk⟩ := quotient_odd hoddK H
      omega
    by_cases hdH : d ∈ H
    · let dH : H := ⟨d, hdH⟩
      have hdH0 : dH ≠ 0 := fun h => hd (congrArg (fun a : H => (a : K)) h)
      letI : Nontrivial H := nontrivial_of_ne dH 0 hdH0
      have hH : 3 ≤ Nat.card H := three_le_of_odd_nontrivial H (subgroup_odd hoddK H)
      obtain ⟨cH, hcH⟩ := hE 0 dH hdH0.symm
      let c' := cH.map H.subtype Subtype.val_injective
      have hrange : H.subtype '' (Set.univ : Set H) = (H : Set K) := by
        ext z
        simp
      let c : RainbowCycle (H : Set K) :=
        ⟨c'.next, (congrArg (fun S : Set K => c'.next.IsCycleOn S) hrange).mp c'.cyclic,
          (congrArg (fun S : Set K => Set.InjOn (fun z => z + c'.next z) S) hrange).mp c'.rainbow⟩
      have hc : c.next 0 = d := by
        have hh := cH.map_next H.subtype Subtype.val_injective 0
        rw [map_zero, hcH] at hh
        exact hh
      obtain ⟨v, hv, hclose⟩ := c.cyclic.1.surjOn H.zero_mem
      have h0v : (0 : K) ≠ v := by
        intro heq
        rw [← heq, hc] at hclose
        exact hd hclose
      obtain ⟨r, hgen⟩ := quotient_generator_lift H
      obtain ⟨C, hpres, _⟩ := cyclic_quotient_glue_controlled hoddK H hH hq hE r hgen
        (H : Set K) (fun _ h => h) c 0 v H.zero_mem hv hclose
      have hset : (H : Set K)ᶜ ∪ (H : Set K) = Set.univ := Set.compl_union_self _
      let C' : RainbowCycle (Set.univ : Set K) :=
        ⟨C.next, (congrArg (fun S : Set K => C.next.IsCycleOn S) hset).mp C.cyclic,
          (congrArg (fun S : Set K => Set.InjOn (fun z => z + C.next z) S) hset).mp C.rainbow⟩
      exact ⟨C', (hpres 0 H.zero_mem h0v).trans hc⟩
    · letI := Fintype.ofFinite (K ⧸ H)
      have hdQ : (QuotientAddGroup.mk d : K ⧸ H) ≠ 0 :=
        fun heq => hdH ((QuotientAddGroup.eq_zero_iff d).mp heq)
      have hgen : ∀ z : K ⧸ H, z ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk d) :=
        fun _ => mem_zmultiples_of_prime_card rfl hdQ
      obtain ⟨cH⟩ := full_cycle_of_edge_property hE
      exact Rows.exists_full_cycle_with_edge hoddK H d hgen cH
        (by simpa only [Nat.card_eq_fintype_card] using hp.one_lt)

end SunTwoDeletion
