import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_15_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 15)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 12) 0 1 2
    (![8, 6, 4, 14, 12, 10, 9, 11, 13, 3, 5, 7] : Fin 12 → ZMod 15)
    (by decide) (by decide) (by decide)

theorem finite_15_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 15)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 12) 0 1 3
    (![9, 11, 13, 5, 7, 8, 6, 4, 2, 14, 12, 10] : Fin 12 → ZMod 15)
    (by decide) (by decide) (by decide)

theorem finite_15_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 15)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 12) 0 1 4
    (![3, 11, 12, 9, 2, 10, 14, 6, 13, 5, 8, 7] : Fin 12 → ZMod 15)
    (by decide) (by decide) (by decide)

theorem finite_15_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 15)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 12) 0 1 5
    (![2, 10, 3, 11, 8, 9, 13, 12, 4, 7, 14, 6] : Fin 12 → ZMod 15)
    (by decide) (by decide) (by decide)

theorem finite_15_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 15)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 12) 0 1 6
    (![10, 11, 12, 13, 7, 8, 9, 2, 14, 5, 4, 3] : Fin 12 → ZMod 15)
    (by decide) (by decide) (by decide)

theorem finite_15_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 15)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 12) 0 1 7
    (![11, 10, 9, 8, 14, 13, 12, 4, 5, 6, 2, 3] : Fin 12 → ZMod 15)
    (by decide) (by decide) (by decide)

theorem finite_15_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 15)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 12) 0 1 8
    (![12, 13, 14, 9, 10, 11, 4, 3, 2, 7, 6, 5] : Fin 12 → ZMod 15)
    (by decide) (by decide) (by decide)

theorem finite_15_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 15)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 12) 0 1 9
    (![12, 11, 10, 14, 13, 5, 6, 7, 8, 2, 3, 4] : Fin 12 → ZMod 15)
    (by decide) (by decide) (by decide)

theorem finite_15_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 15)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 12) 0 1 10
    (![14, 2, 11, 12, 13, 6, 5, 4, 3, 9, 8, 7] : Fin 12 → ZMod 15)
    (by decide) (by decide) (by decide)

theorem finite_15_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 15)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 12) 0 1 11
    (![3, 4, 12, 9, 2, 10, 14, 6, 13, 5, 8, 7] : Fin 12 → ZMod 15)
    (by decide) (by decide) (by decide)

theorem finite_15_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 15)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 12) 0 1 12
    (![2, 10, 3, 11, 8, 9, 13, 5, 4, 7, 14, 6] : Fin 12 → ZMod 15)
    (by decide) (by decide) (by decide)

theorem finite_15_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 15)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 12) 0 1 13
    (![8, 10, 12, 14, 2, 4, 6, 7, 5, 3, 11, 9] : Fin 12 → ZMod 15)
    (by decide) (by decide) (by decide)

theorem finite_15_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 15)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 12) 0 1 14
    (![7, 5, 3, 13, 11, 9, 8, 10, 12, 2, 4, 6] : Fin 12 → ZMod 15)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
