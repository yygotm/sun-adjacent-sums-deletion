import SunThreeDeletion.PrimeLine

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion
variable {G : Type*} [AddCommGroup G] [Finite G]

theorem prime_subgroup_generator (H : AddSubgroup G) (hp : (Nat.card H).Prime)
    (d : G) (hd : d≠0) (hm : d∈H) : H=AddSubgroup.zmultiples d := by
  haveI : Fact (Nat.card H).Prime := ⟨hp⟩
  apply le_antisymm
  · intro x hx
    let dH : H := ⟨d,hm⟩
    have hdH : dH≠0 := fun h => hd (congrArg (fun x : H => (x:G)) h)
    obtain ⟨n,hn⟩ := mem_zmultiples_of_prime_card rfl (g' := (⟨x,hx⟩ : H)) hdH
    refine ⟨n,?_⟩
    exact congrArg (fun x : H => (x:G)) hn
  · exact AddSubgroup.zmultiples_le.mpr hm

theorem small_subgroup_line (hodd : Odd (Nat.card G)) (hcard : 7 ≤ Nat.card G)
    (H : AddSubgroup G) (hH : Nat.card H=3 ∨ Nat.card H=5)
    (d : H) (hd : d≠0) :
    HasRainbowCycle ({0,(d:G),2 • (d:G)}ᶜ : Set G) := by
  have hproper : H≠⊤ := by
    intro h
    have hc := (AddSubgroup.card_eq_iff_eq_top H).mpr h
    rcases hH with hH | hH <;> omega
  obtain ⟨K,hHK,hq⟩ := prime_overgroup H hproper
  let J := H.addSubgroupOf K
  let dK : K := ⟨d,hHK d.property⟩
  have hJ : Nat.card J=Nat.card H :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hHK).toEquiv
  have hdK : dK≠0 := by
    intro h
    exact hd (Subtype.ext (congrArg (fun x : K => (x:G)) h))
  have hJprime : (Nat.card J).Prime := by
    rw [hJ]; rcases hH with hH | hH <;> rw [hH] <;> decide
  have hJd : J=AddSubgroup.zmultiples dK :=
    prime_subgroup_generator J hJprime dK hdK d.property
  have hcycle : HasRainbowCycle ({0,dK,2 • dK}ᶜ : Set K) := by
    rcases hH with hH | hH
    · exact line_extension_three (subgroup_odd hodd K) J (hJ.trans hH) hq dK hdK hJd
    · exact line_extension_five (subgroup_odd hodd K) J (hJ.trans hH) hq dK hdK hJd
  have hK : 4 ≤ Nat.card K := by
    have hc := J.card_eq_card_quotient_mul_card_addSubgroup
    have hqp := hq.two_le
    change 2 ≤ Nat.card (K ⧸ J) at hqp
    rcases hH with hH | hH <;> rw [hJ,hH] at hc <;> omega
  have hh := lift_three_cycle hodd K hK 0 dK (2 • dK) hcycle
  simpa only [AddSubgroup.coe_zero,AddSubgroup.coe_nsmul] using hh

theorem small_subgroup_three (hodd : Odd (Nat.card G)) (hcard : 7 ≤ Nat.card G)
    (H : AddSubgroup G) (hH : Nat.card H=3 ∨ Nat.card H=5)
    (a b c : H) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    HasRainbowCycle ({(a:G),(b:G),(c:G)}ᶜ : Set G) := by
  obtain ⟨s,d,hd,he⟩ := small_prime_triple_ap hH a b c hab hac hbc
  have hh := small_subgroup_line hodd hcard H hH d hd
  have hh' := affine_three_cycle (AddEquiv.refl G) (s:G) 0 (d:G) (2 • (d:G)) hh
  have he' := congrArg (fun A : Set H => H.subtype '' A) he
  simp only [Set.image_insert_eq,Set.image_singleton,AddSubgroup.coe_add,
    AddSubgroup.coe_nsmul,AddSubgroup.subtype_apply] at he'
  have ht : ({0+(s:G),(d:G)+(s:G),2 • (d:G)+(s:G)} : Set G) =
      {(a:G),(b:G),(c:G)} := by
    rw [he']
    simp only [zero_add,add_zero,add_comm]
  simpa only [AddEquiv.refl_apply,ht] using hh'

end SunThreeDeletion
