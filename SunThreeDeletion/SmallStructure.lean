import SunThreeDeletion.PrimeCoordinates
import SunThreeDeletion.PrimeOvergroup

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion
variable {G : Type*} [AddCommGroup G] [Finite G]

theorem span_of_prime_quotient (H : AddSubgroup G)
    (hp : (Nat.card (G ⧸ H)).Prime) (d : G) (hd : H=AddSubgroup.zmultiples d)
    (r : G) (hr : r ∉ H) :
    AddSubgroup.zmultiples d ⊔ AddSubgroup.zmultiples r=⊤ := by
  haveI : Fact (Nat.card (G ⧸ H)).Prime := ⟨hp⟩
  have hn : (QuotientAddGroup.mk r : G ⧸ H) ≠ 0 :=
    fun h => hr ((QuotientAddGroup.eq_zero_iff r).mp h)
  apply top_unique
  intro x _
  obtain ⟨n,hnx⟩ := mem_zmultiples_of_prime_card rfl (g' := (QuotientAddGroup.mk x : G ⧸ H)) hn
  change n • (QuotientAddGroup.mk r : G ⧸ H)=QuotientAddGroup.mk x at hnx
  have hm : x-n • r ∈ H := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change (QuotientAddGroup.mk' H) (x-n • r)=0
    rw [map_sub,map_zsmul]
    exact sub_eq_zero.mpr hnx.symm
  have hm' : x-n • r ∈ AddSubgroup.zmultiples d := hd ▸ hm
  have hh := (AddSubgroup.zmultiples d ⊔ AddSubgroup.zmultiples r).add_mem
    (AddSubgroup.mem_sup_left hm')
    (AddSubgroup.mem_sup_right ((AddSubgroup.zmultiples r).zsmul_mem (AddSubgroup.mem_zmultiples r) n))
  simpa using hh

theorem cyclic_coprime_extension (H : AddSubgroup G) [IsAddCyclic H]
    [IsAddCyclic (G ⧸ H)] (hc : (Nat.card H).Coprime (Nat.card (G ⧸ H))) :
    IsAddCyclic G := by
  let f := QuotientAddGroup.mk' H
  have he : f.ker=H := by ext x; exact QuotientAddGroup.eq_zero_iff x
  haveI : IsAddCyclic f.ker := he.symm ▸ inferInstance
  apply AddGroup.isAddCyclic_of_coprime_card_ker f
  · simpa only [he] using hc
  · exact QuotientAddGroup.mk'_surjective H

theorem noncyclic_prime_square_nsmul (p : ℕ) [Fact p.Prime]
    (hc : Nat.card G=p^2) (hn : ¬ IsAddCyclic G) (x : G) : p • x=0 := by
  have hd := addOrderOf_dvd_natCard x
  rw [hc,Nat.dvd_prime_pow (Fact.out : p.Prime)] at hd
  obtain ⟨k,hk,he⟩ := hd
  have hk' : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases hk' with rfl | rfl | rfl
  · apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    simp [he]
  · apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    simp [he]
  · exact (hn (isAddCyclic_of_addOrderOf_eq_card x (he.trans hc.symm))).elim

theorem prime_square_coordinates (p : ℕ) [Fact p.Prime]
    (H : AddSubgroup G) (hH : Nat.card H=p) (hq : Nat.card (G ⧸ H)=p)
    (d : G) (hd : d ≠ 0) (hHd : H=AddSubgroup.zmultiples d)
    (hn : ¬ IsAddCyclic G) :
    ∃ e : (ZMod p × ZMod p) ≃+ G, e (1,0)=d := by
  have hc : Nat.card G=p^2 := by
    rw [H.card_eq_card_quotient_mul_card_addSubgroup,hH,hq,pow_two]
  have hproper : H ≠ ⊤ := by
    intro h
    have he : Nat.card H=Nat.card G := by rw [h]; exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
    have hp := (Fact.out : p.Prime).two_le
    nlinarith
  obtain ⟨r,hr⟩ : ∃ r : G, r ∉ H := by
    by_contra h
    push_neg at h
    exact hproper (top_unique (fun x _ => h x))
  have hs := span_of_prime_quotient H (hq ▸ (Fact.out : p.Prime)) d hHd r hr
  obtain ⟨e,he,_⟩ := prime_pair_coordinates p d r hd
    (noncyclic_prime_square_nsmul p hc hn d)
    (noncyclic_prime_square_nsmul p hc hn r) (by rwa [← hHd]) hs
  exact ⟨e,he⟩

end SunThreeDeletion
