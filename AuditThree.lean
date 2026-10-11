import SunThreeDeletion

set_option autoImplicit false

#check @SunThreeDeletion.sun_three_deletion
#print SunTwoDeletion.cyclicSuccessor
#check SunThreeDeletion.cyclicSuccessor_last
#print axioms SunThreeDeletion.sun_three_deletion
#print axioms SunThreeDeletion.three_deletion_cycle
#print axioms SunThreeDeletion.q1_cycle
#print axioms SunThreeDeletion.q3_cycle
#print axioms SunThreeDeletion.boundary1_of_not_interior
#print axioms SunThreeDeletion.boundary3_of_not_interior
#print axioms SunThreeDeletion.cyclic_finite_base
#print axioms SunThreeDeletion.subgroup_extension
#print axioms SunThreeDeletion.two_punctured_fibers
#print axioms SunThreeDeletion.three_punctured_fibers
#print axioms SunThreeDeletion.line_extension_three
#print axioms SunThreeDeletion.line_extension_five

/-- An independently spelled output contract: fixed length and a literal
modulo expression instead of the library's cyclic successor definition. -/
theorem checked_literal_contract (G : Type*) [AddCommGroup G] [Finite G]
    (hodd : Odd (Nat.card G)) (hsize : 2 < Nat.card G-3)
    (a b c : G) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    ∃ v : Fin (Nat.card G-3) ↪ G,
      Set.range v=({a,b,c}ᶜ : Set G) ∧
      Function.Injective (fun i =>
        v i + v ⟨(i.val+1) % (Nat.card G-3), Nat.mod_lt _ (by omega)⟩) := by
  obtain ⟨n,hn,v,heq,_,hr,hi⟩ := SunThreeDeletion.sun_three_deletion hodd hsize a b c hab hac hbc
  subst n
  refine ⟨v,hr,?_⟩
  have he (i : Fin (Nat.card G-3)) :
      SunTwoDeletion.cyclicSuccessor hn i =
        ⟨(i.val+1) % (Nat.card G-3), Nat.mod_lt _ (by omega)⟩ :=
    Fin.ext (SunTwoDeletion.cyclicSuccessor_val hn i)
  simpa only [he] using hi

#print axioms checked_literal_contract
