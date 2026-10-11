import AuditTwo
import AuditThree
import SunFourDeletion
import AuditExamples

set_option autoImplicit false

#check @SunTwoDeletion.sun_two_deletion_exact
#check @SunTwoDeletion.sun_two_deletion_ordering
#check @SunThreeDeletion.sun_three_deletion
#check @SunFourDeletion.sun_four_deletion
#check @SunFourDeletion.sun_four_deletion_finset
#print SunTwoDeletion.cyclicSuccessor

/-- An independently spelled contract, with fixed length and literal modulo successor. -/
theorem checked_literal_four_contract (G : Type*) [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (hsize : 7 ≤ Nat.card G)
    (a b c d : G) (hab : a≠b) (hac : a≠c) (had : a≠d)
    (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    ∃ v : Fin (Nat.card G-4) ↪ G,
      Set.range v=({a,b,c,d}ᶜ : Set G) ∧
      Function.Injective (fun i =>
        v i + v ⟨(i.val+1) % (Nat.card G-4), Nat.mod_lt _ (by omega)⟩) := by
  obtain ⟨n,hn,v,heq,_,hr,hi⟩ :=
    SunFourDeletion.sun_four_deletion hodd hsize a b c d hab hac had hbc hbd hcd
  subst n
  refine ⟨v,hr,?_⟩
  have he (i : Fin (Nat.card G-4)) :
      SunTwoDeletion.cyclicSuccessor hn i =
        ⟨(i.val+1) % (Nat.card G-4), Nat.mod_lt _ (by omega)⟩ :=
    Fin.ext (SunTwoDeletion.cyclicSuccessor_val hn i)
  simpa only [he] using hi

/-- Concrete use of the unconditional main theorem. -/
theorem zmod_nine_four_deletion :
    ∃ (n : ℕ) (hn : 0<n) (v : Fin n ↪ ZMod 9),
      n=5 ∧ 2<n ∧ Set.range v=({0,1,2,3}ᶜ : Set (ZMod 9)) ∧
      Function.Injective (fun i => v i+v (SunTwoDeletion.cyclicSuccessor hn i)) := by
  simpa only [Nat.card_zmod] using
    SunFourDeletion.sun_four_deletion (G := ZMod 9) (by norm_num [Nat.card_zmod])
      (by norm_num [Nat.card_zmod]) 0 1 2 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The boundary |G|=7 is included: exactly three vertices remain. -/
theorem zmod_seven_four_deletion :
    ∃ (n : ℕ) (hn : 0<n) (v : Fin n ↪ ZMod 7),
      n=3 ∧ 2<n ∧ Set.range v=({0,1,2,3}ᶜ : Set (ZMod 7)) ∧
      Function.Injective (fun i => v i+v (SunTwoDeletion.cyclicSuccessor hn i)) := by
  simpa only [Nat.card_zmod] using
    SunFourDeletion.sun_four_deletion (G := ZMod 7) (by norm_num [Nat.card_zmod])
      (by norm_num [Nat.card_zmod]) 0 1 2 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- Explicit positive certificate [4,5,6,7,8] and negative certificate
-- [4,5,6,8,7].  The latter has distinct internal sums; only the closing
-- edge collides. AuditExamples proves the predicate rejects it.
example : SunFourDeletion.RainbowEnumeration (by decide : 0<5)
    ({0,1,2,3}ᶜ : Set (ZMod 9)) SunFourDeletion.goodNine :=
  SunFourDeletion.goodNine_valid

example : ¬ SunFourDeletion.RainbowEnumeration (by decide : 0<5)
    ({0,1,2,3}ᶜ : Set (ZMod 9)) SunFourDeletion.badNine :=
  SunFourDeletion.badNine_rejected

#print axioms SunTwoDeletion.sun_two_deletion_exact
#print axioms SunTwoDeletion.sun_two_deletion_ordering
#print axioms SunThreeDeletion.sun_three_deletion
#print axioms SunFourDeletion.sun_four_deletion
#print axioms SunFourDeletion.sun_four_deletion_finset
#print axioms SunFourDeletion.four_deletion_cycle
#print axioms SunFourDeletion.odd_cyclic_subset
#print axioms SunFourDeletion.glue_one_full_fiber
#print axioms SunFourDeletion.missed_prime_quotient
#print axioms SunFourDeletion.plane_four
#print axioms SunFourDeletion.plane_five_cycle
#print axioms SunFourDeletion.one_hole
#print axioms checked_literal_four_contract
#print axioms zmod_nine_four_deletion
#print axioms zmod_seven_four_deletion
#print axioms SunFourDeletion.goodNine_valid
#print axioms SunFourDeletion.badNine_rejected
