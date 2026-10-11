import SunThreeDeletion.QBoundary

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace SunThreeDeletion

theorem bad_bounds (s : ℤ) (h : BadRepresentative s) : -8 ≤ s ∧ s ≤ 4 ∧ s ≠ 0 ∧ s ≠ -2 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem bad_product_bounds (u v : ℤ) (hu : BadRepresentative u) (hv : BadRepresentative v) :
    -48 ≤ u*v-16 ∧ u*v-16 ≤ 48 := by
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

theorem bad_product_eq (u v : ℤ) (hu : BadRepresentative u) (hv : BadRepresentative v)
    (h : u*v = 16) : u = 4 ∧ v = 4 := by
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num at *

theorem small_divisible_zero (m z : ℤ) (hm : 49 ≤ m) (hz : -48 ≤ z ∧ z ≤ 48)
    (hd : m ∣ z) : z = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
  omega

/-- The bounded integer obstruction rules out simultaneous failure of all three anchors. -/
theorem no_three_bad_anchors (m u v w : ℤ) (hm : 49 ≤ m)
    (hu : BadRepresentative u) (hv : BadRepresentative v) (hw : BadRepresentative w)
    (h1 : m ∣ u*v-16) (h2 : m ∣ (u+4)*w+16) : False := by
  have heq := small_divisible_zero m (u*v-16) hm (bad_product_bounds u v hu hv) h1
  obtain ⟨rfl, rfl⟩ := bad_product_eq u v hu hv (by omega)
  have hw' := bad_bounds w hw
  have hz : -48 ≤ (4+4)*w+16 ∧ (4+4)*w+16 ≤ 48 := by omega
  have heq2 := small_divisible_zero m ((4+4)*w+16) hm hz h2
  omega

theorem no_bad_order_three (m s : ℤ) (hm : 49 ≤ m)
    (hs : BadRepresentative s) (hd : m ∣ 3*s) : False := by
  have hs' := bad_bounds s hs
  have h := small_divisible_zero m (3*s) hm (by omega) hd
  omega

end SunThreeDeletion

