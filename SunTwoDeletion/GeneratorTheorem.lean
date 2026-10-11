import SunTwoDeletion.Deletion

set_option autoImplicit false

namespace SunTwoDeletion

variable {G : Type*} [AddCommGroup G] [Finite G]

/-- Unconditional exact theorem for a pair whose difference generates the group. -/
theorem exact_two_deletion_of_generator_difference
    (hodd : Odd (Nat.card G)) (hsize : 2 < Nat.card G - 2)
    (a b : G) (hab : a ≠ b)
    (hgen : ∀ x : G, x ∈ AddSubgroup.zmultiples (b - a)) :
    ∃ c : RainbowCycle ({a, b}ᶜ : Set G),
      c.colors = ({3 • a - b, 3 • b - a}ᶜ : Set G) := by
  have hd : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have h3 := generator_three_nonzero (b - a) hgen (by omega : 3 < Nat.card G)
  let c := twoGeneratorCycle hodd (b - a) hd h3 hgen
  let t := c.translate a
  have hA : (fun x : G => x + a) '' ({0, b - a}ᶜ : Set G) = ({a, b}ᶜ : Set G) := by
    simpa only [zero_add, sub_add_cancel] using translate_compl_pair (0 : G) (b - a) a
  let result : RainbowCycle ({a, b}ᶜ : Set G) :=
    ⟨t.next, by rw [← hA]; exact t.cyclic, by rw [← hA]; exact t.rainbow⟩
  refine ⟨result, ?_⟩
  have ht : result.colors = t.colors := by
    change (fun x => x + t.next x) '' ({a, b}ᶜ : Set G) =
      (fun x => x + t.next x) '' ((fun x => x + a) '' ({0, b - a}ᶜ : Set G))
    exact congrArg (fun S : Set G => (fun x => x + t.next x) '' S) hA.symm
  rw [ht, RainbowCycle.translate_colors, twoGeneratorCycle_colors,
    translate_compl_pair]
  have hleft : -(b - a) + (a + a) = 3 • a - b := by abel
  have hright : ((b - a) + (b - a) + (b - a)) + (a + a) = 3 • b - a := by abel
  rw [hleft, hright]

/-- The two-deletion theorem holds in every odd prime order. -/
theorem exact_two_deletion_prime (hprime : (Nat.card G).Prime) :
    ExactTwoDeletionStatement G := by
  intro hodd hsize a b hab
  letI : Fact (Nat.card G).Prime := ⟨hprime⟩
  apply exact_two_deletion_of_generator_difference hodd hsize a b hab
  exact fun _ => mem_zmultiples_of_prime_card rfl (sub_ne_zero.mpr hab.symm)

end SunTwoDeletion
