import SunThreeDeletion.SmallLine
import SunThreeDeletion.ThreeFibers
import SunThreeDeletion.QuotientLift

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion
variable {G : Type*} [AddCommGroup G] [Finite G]

theorem product_line_cycle (p : ℕ) (hp : p=3 ∨ p=5)
    (d : G) (e : (ZMod p × ZMod p) ≃+ G) (he : e (1,0)=d) :
    HasRainbowCycle ({0,d,2 • d}ᶜ : Set G) := by
  have hb : HasRainbowCycle ({(0,0),(1,0),(2,0)}ᶜ : Set (ZMod p × ZMod p)) := by
    rcases hp with rfl | rfl
    · exact base_C3xC3_line
    · exact base_C5xC5_line
  have h2 : e (2,0)=2 • d := by
    have hh : e (2 • (1,0))=2 • e (1,0) := map_nsmul e _ _
    simpa only [two_nsmul,Prod.mk_add_mk,one_add_one_eq_two,add_zero,he] using hh
  have hh := affine_three_cycle e 0 (0,0) (1,0) (2,0) hb
  have h0 : e (0,0)=0 := e.map_zero
  simpa only [h0,he,h2,zero_add,add_zero] using hh

theorem order_three_subgroup_set (hodd : Odd (Nat.card G))
    (H : AddSubgroup G) (hH : Nat.card H=3)
    (d : G) (hd : d≠0) (hm : d∈H) :
    (H : Set G)={0,d,2 • d} := by
  have hd2 : d≠2 • d := by
    intro h
    apply hd
    have hh : d+0=d+d := by simpa only [two_nsmul,add_zero] using h
    exact (add_left_cancel hh).symm
  have h20 : 2 • d≠0 := fun h => hd (double_injective hodd (by simpa only [two_nsmul,add_zero] using h))
  have hs : ({0,d,2 • d} : Set G) ⊆ H := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact H.zero_mem
    · exact hm
    · exact H.nsmul_mem hm 2
  apply Eq.symm
  apply Set.eq_of_subset_of_ncard_le hs
  have hh : (H : Set G).ncard=3 := hH
  rw [hh]
  simp [Set.ncard_insert_of_notMem,hd,hd.symm,h20,h20.symm,hd2]

theorem line_extension_three (hodd : Odd (Nat.card G))
    (H : AddSubgroup G) (hH : Nat.card H=3)
    (hq : (Nat.card (G ⧸ H)).Prime)
    (d : G) (hd : d≠0) (hHd : H=AddSubgroup.zmultiples d) :
    HasRainbowCycle ({0,d,2 • d}ᶜ : Set G) := by
  have hm : d∈H := hHd.symm ▸ AddSubgroup.mem_zmultiples d
  haveI : Fact (Nat.card (G ⧸ H)).Prime := ⟨hq⟩
  haveI : IsAddCyclic (G ⧸ H) := isAddCyclic_of_prime_card rfl
  have hoq := quotient_odd hodd H
  have hqp := hq.two_le
  by_cases h3 : Nat.card (G ⧸ H)=3
  · by_cases hcyc : IsAddCyclic G
    · haveI := hcyc
      have hc : Nat.card G=9 := by rw [H.card_eq_card_quotient_mul_card_addSubgroup,hH,h3]
      have hp : 3 • d=0 := by
        have hh : Nat.card H • (⟨d,hm⟩ : H)=0 := card_nsmul_eq_zero'
        have hh' := congrArg (fun x : H => (x:G)) hh
        simpa only [AddSubgroup.coe_nsmul,AddSubgroup.coe_zero,hH] using hh'
      exact small_cyclic_line 3 3 (Or.inl ⟨hc,rfl,rfl⟩) d hd hp
    · obtain ⟨e,he⟩ := prime_square_coordinates 3 H hH h3 d hd hHd hcyc
      exact product_line_cycle 3 (Or.inl rfl) d e he
  · have hbig : 5 ≤ Nat.card (G ⧸ H) := by obtain ⟨k,hk⟩ := hoq; omega
    haveI : Nontrivial (G ⧸ H) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have hne : ({0}ᶜ : Set (G ⧸ H)).Nonempty := by
      obtain ⟨x,hx⟩ := exists_ne (0 : G ⧸ H)
      exact ⟨x,hx⟩
    have hc := one_hole_cyclic_group (G ⧸ H) hoq hbig
    have hh := quotient_preimage_cycle hodd H ({0}ᶜ : Set (G ⧸ H)) hne hc
    have heq : (QuotientAddGroup.mk' H) ⁻¹' ({0}ᶜ : Set (G ⧸ H))=(H : Set G)ᶜ := by
      ext x
      simp only [Set.mem_preimage,Set.mem_compl_iff,Set.mem_singleton_iff]
      exact not_congr (QuotientAddGroup.eq_zero_iff x)
    change HasRainbowCycle ((QuotientAddGroup.mk' H) ⁻¹' ({0}ᶜ : Set (G ⧸ H))) at hh
    rw [heq,order_three_subgroup_set hodd H hH d hd hm] at hh
    exact hh

theorem line_extension_five (hodd : Odd (Nat.card G))
    (H : AddSubgroup G) (hH : Nat.card H=5)
    (hq : (Nat.card (G ⧸ H)).Prime)
    (d : G) (hd : d≠0) (hHd : H=AddSubgroup.zmultiples d) :
    HasRainbowCycle ({0,d,2 • d}ᶜ : Set G) := by
  have hm : d∈H := hHd.symm ▸ AddSubgroup.mem_zmultiples d
  have hp : 5 • d=0 := by
    have hh : Nat.card H • (⟨d,hm⟩ : H)=0 := card_nsmul_eq_zero'
    have hh' := congrArg (fun x : H => (x:G)) hh
    simpa only [AddSubgroup.coe_nsmul,AddSubgroup.coe_zero,hH] using hh'
  haveI : Fact (Nat.card (G ⧸ H)).Prime := ⟨hq⟩
  haveI : IsAddCyclic (G ⧸ H) := isAddCyclic_of_prime_card rfl
  haveI : IsAddCyclic H := by rw [hHd]; infer_instance
  by_cases h3 : Nat.card (G ⧸ H)=3
  · haveI : IsAddCyclic G := cyclic_coprime_extension H (by rw [hH,h3]; decide)
    have hc : Nat.card G=15 := by rw [H.card_eq_card_quotient_mul_card_addSubgroup,hH,h3]
    exact small_cyclic_line 5 3 (Or.inr (Or.inl ⟨hc,rfl,rfl⟩)) d hd hp
  by_cases h5 : Nat.card (G ⧸ H)=5
  · by_cases hcyc : IsAddCyclic G
    · haveI := hcyc
      have hc : Nat.card G=25 := by rw [H.card_eq_card_quotient_mul_card_addSubgroup,hH,h5]
      exact small_cyclic_line 5 5 (Or.inr (Or.inr ⟨hc,rfl,rfl⟩)) d hd hp
    · haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
      obtain ⟨e,he⟩ := prime_square_coordinates 5 H hH h5 d hd hHd hcyc
      exact product_line_cycle 5 (Or.inr rfl) d e he
  have hqbig : 7 ≤ Nat.card (G ⧸ H) := by
    have := hq.two_le
    obtain ⟨k,hk⟩ := quotient_odd hodd H
    omega
  obtain ⟨r,hr⟩ := exists_prime_addOrderOf_dvd_card' (G := G)
    (Nat.card (G ⧸ H)) H.card_quotient_dvd_card
  let J := AddSubgroup.zmultiples r
  have hJ : Nat.card J=Nat.card (G ⧸ H) := by rw [Nat.card_zmultiples,hr]
  have hJq : Nat.card (G ⧸ J)=5 := by
    have hc1 := H.card_eq_card_quotient_mul_card_addSubgroup
    have hc2 := J.card_eq_card_quotient_mul_card_addSubgroup
    rw [hH] at hc1
    rw [hJ] at hc2
    nlinarith
  have hdJ : d ∉ J := by
    intro hdJ
    have hle : H ≤ J := by rw [hHd]; exact AddSubgroup.zmultiples_le.mpr hdJ
    have hdiv := AddSubgroup.card_dvd_of_le hle
    rw [hH,hJ] at hdiv
    have he := (Nat.dvd_prime hq).mp hdiv
    omega
  haveI : Fact (Nat.card (G ⧸ J)).Prime := ⟨by rw [hJq]; decide⟩
  have hgen : ∀ x : G ⧸ J, x∈AddSubgroup.zmultiples (QuotientAddGroup.mk d) := by
    intro x
    exact mem_zmultiples_of_prime_card rfl (fun h => hdJ ((QuotientAddGroup.eq_zero_iff d).mp h))
  obtain ⟨C⟩ := one_hole_cyclic_group J (subgroup_odd hodd J) (by omega)
  exact three_punctured_fibers hodd J (by omega) (by omega) d hgen C

end SunThreeDeletion
