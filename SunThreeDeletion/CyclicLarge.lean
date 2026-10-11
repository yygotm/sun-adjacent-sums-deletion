import SunThreeDeletion.AffineTemplates
import SunThreeDeletion.SmallObstruction

set_option autoImplicit false
namespace SunThreeDeletion
open SunTwoDeletion

/-- An affine Q template fails only when its cross-ratio has a small residue.
The equation is written without division and remains meaningful over composite moduli. -/
theorem affine_obstruction (m : ℕ) (hodd : Odd m) (hm : 49 ≤ m)
    (a b c : ZMod m) (hab : a ≠ b) (hac : a ≠ c)
    (hunit : IsUnit (c-b))
    (hfail : ¬ HasRainbowCycle ({a,b,c}ᶜ : Set (ZMod m))) :
    ∃ s : ℤ, BadRepresentative s ∧ (s : ZMod m)*(c-b) = 4*(b-a) := by
  obtain ⟨u, hu⟩ := hunit
  let two : (ZMod m)ˣ := ZMod.unitOfCoprime 2 hodd.coprime_two_left
  have htwo : (two : ZMod m) = 2 := by simp [two]
  let v : (ZMod m)ˣ := two⁻¹ * u
  have hv : (2 : ZMod m)*(v : ZMod m) = c-b := by
    calc
      (2 : ZMod m)*(v : ZMod m) = (two : ZMod m)*(v : ZMod m) := by rw [htwo]
      _ = (u : ZMod m) := by simp [v, ← mul_assoc]
      _ = c-b := hu
  let t : ZMod m := (b-a) * ↑(v⁻¹)
  have htv : t*(v : ZMod m) = b-a := by simp [t, mul_assoc]
  have htv2 : (t+2)*(v : ZMod m) = c-a := by rw [add_mul, htv, hv]; ring
  have ht : t ≠ 0 := by
    intro h
    rw [h, zero_mul] at htv
    exact hab (sub_eq_zero.mp htv.symm).symm
  have ht2 : t+2 ≠ 0 := by
    intro h
    rw [h, zero_mul] at htv2
    exact hac (sub_eq_zero.mp htv2.symm).symm
  rcases cyclic_zmod_delete_or_bad m hodd hm t ht ht2 with h | h
  · exfalso
    apply hfail
    have hh := affine_three_cycle (AddAut.mulRight v) a 0 t (t+2) h
    simpa only [AddAut.mulRight_apply, zero_mul, zero_add, htv, htv2, sub_add_cancel] using hh
  · obtain ⟨s, hs, he⟩ := h
    refine ⟨s, hs, ?_⟩
    calc
      (s : ZMod m)*(c-b) = (2*t)*(2*(v : ZMod m)) := by rw [he, hv]
      _ = 4*(t*(v : ZMod m)) := by ring
      _ = 4*(b-a) := by rw [htv]

theorem cyclic_large_units (m : ℕ) (hodd : Odd m) (hm : 49 ≤ m)
    (t : ZMod m) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hu : IsUnit t) (hv : IsUnit (t-1)) :
    HasRainbowCycle ({0,1,t}ᶜ : Set (ZMod m)) := by
  haveI : Fact (1 < m) := ⟨by omega⟩
  by_contra hfail
  have hf1 : ¬ HasRainbowCycle ({t,0,1}ᶜ : Set (ZMod m)) := by
    have hset : ({t,0,1} : Set (ZMod m)) = {0,1,t} := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [hset]
  have hf2 : ¬ HasRainbowCycle ({1,0,t}ᶜ : Set (ZMod m)) := by
    simpa only [Set.insert_comm] using hfail
  obtain ⟨u, huS, hue⟩ := affine_obstruction m hodd hm t 0 1 ht0 ht1
    (by simpa using (isUnit_one : IsUnit (1 : ZMod m))) hf1
  obtain ⟨v, hvS, hve⟩ := affine_obstruction m hodd hm 1 0 t one_ne_zero ht1.symm
    (by simpa using hu) hf2
  obtain ⟨w, hwS, hwe⟩ := affine_obstruction m hodd hm 0 1 t zero_ne_one ht0.symm hv hfail
  have huez : (u : ZMod m) = -4*t := by simpa using hue
  have hvez : (v : ZMod m)*t = -4 := by simpa using hve
  have hwez : (w : ZMod m)*(t-1) = 4 := by simpa using hwe
  have he1 : ((u*v-16 : ℤ) : ZMod m) = 0 := by
    push_cast
    rw [huez]
    linear_combination -4*hvez
  have he2 : (((u+4)*w+16 : ℤ) : ZMod m) = 0 := by
    push_cast
    rw [huez]
    linear_combination -4*hwez
  exact no_three_bad_anchors m u v w (by exact_mod_cast hm) huS hvS hwS
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp he1)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp he2)

theorem cyclic_large_order_three (m : ℕ) (hodd : Odd m) (hm : 49 ≤ m)
    (t : ZMod m) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (h3 : 3*t=0) :
    HasRainbowCycle ({0,1,t}ᶜ : Set (ZMod m)) := by
  haveI : Fact (1 < m) := ⟨by omega⟩
  by_contra hfail
  have hf : ¬ HasRainbowCycle ({t,0,1}ᶜ : Set (ZMod m)) := by
    have hset : ({t,0,1} : Set (ZMod m)) = {0,1,t} := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [hset]
  obtain ⟨s, hs, he⟩ := affine_obstruction m hodd hm t 0 1 ht0 ht1
    (by simpa using (isUnit_one : IsUnit (1 : ZMod m))) hf
  have heq : (s : ZMod m) = -4*t := by simpa using he
  have hzero : ((3*s : ℤ) : ZMod m) = 0 := by
    push_cast
    rw [heq]
    linear_combination -4*h3
  exact no_bad_order_three m s (by exact_mod_cast hm) hs
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp hzero)

end SunThreeDeletion


