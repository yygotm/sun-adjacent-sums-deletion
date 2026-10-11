import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_23_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 2
    (![12, 10, 8, 6, 4, 22, 20, 18, 16, 14, 13, 15, 17, 19, 21, 3, 5, 7, 9, 11] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 3
    (![6, 20, 17, 14, 21, 18, 15, 12, 9, 19, 22, 2, 5, 8, 11, 4, 7, 10, 13, 16] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 4
    (![18, 21, 7, 10, 3, 6, 9, 12, 15, 5, 2, 22, 19, 16, 13, 20, 17, 14, 11, 8] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 5
    (![17, 12, 7, 2, 20, 15, 19, 14, 9, 4, 22, 8, 13, 18, 10, 6, 11, 16, 21, 3] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 6
    (![7, 12, 17, 22, 4, 9, 5, 10, 15, 20, 2, 16, 11, 19, 14, 18, 13, 8, 3, 21] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 7
    (![5, 21, 14, 16, 17, 10, 3, 19, 12, 20, 4, 11, 18, 2, 9, 8, 15, 22, 6, 13] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 8
    (![22, 14, 6, 21, 13, 5, 16, 15, 7, 3, 11, 19, 4, 12, 20, 9, 17, 2, 10, 18] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 9
    (![2, 10, 18, 3, 11, 19, 8, 16, 17, 21, 13, 5, 20, 12, 4, 15, 7, 22, 14, 6] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 10
    (![16, 17, 18, 19, 20, 21, 11, 12, 13, 14, 15, 4, 3, 2, 22, 9, 8, 7, 6, 5] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 11
    (![14, 21, 8, 18, 10, 20, 7, 17, 4, 9, 22, 12, 2, 15, 5, 13, 3, 16, 6, 19] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 12
    (![18, 19, 20, 21, 22, 13, 14, 15, 16, 17, 6, 5, 4, 3, 2, 11, 10, 9, 8, 7] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 13
    (![3, 15, 4, 16, 5, 17, 12, 2, 14, 20, 8, 19, 7, 18, 6, 11, 22, 10, 21, 9] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 14
    (![20, 21, 22, 2, 15, 16, 17, 18, 19, 8, 7, 6, 5, 4, 3, 13, 12, 11, 10, 9] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 15
    (![3, 11, 19, 4, 12, 20, 9, 17, 2, 10, 18, 22, 14, 6, 21, 13, 5, 16, 8, 7] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 16
    (![21, 13, 5, 20, 12, 4, 15, 7, 22, 14, 6, 2, 10, 18, 3, 11, 19, 8, 9, 17] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 17
    (![4, 20, 13, 6, 22, 15, 16, 9, 2, 18, 11, 19, 3, 10, 8, 7, 14, 21, 5, 12] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 18
    (![10, 4, 21, 15, 9, 3, 17, 11, 5, 22, 16, 13, 19, 2, 8, 14, 20, 6, 12, 7] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_19 : HasRainbowCycle ({0, 1, 19}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 19
    (![16, 11, 6, 14, 18, 13, 8, 3, 21, 7, 12, 17, 22, 4, 9, 5, 10, 15, 20, 2] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_20 : HasRainbowCycle ({0, 1, 20}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 20
    (![19, 22, 2, 5, 8, 11, 4, 7, 10, 13, 16, 6, 3, 17, 14, 21, 18, 15, 12, 9] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_21 : HasRainbowCycle ({0, 1, 21}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 21
    (![5, 2, 22, 19, 16, 13, 20, 17, 14, 11, 8, 18, 4, 7, 10, 3, 6, 9, 12, 15] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

theorem finite_23_22 : HasRainbowCycle ({0, 1, 22}ᶜ : Set (ZMod 23)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 20) 0 1 22
    (![11, 9, 7, 5, 3, 21, 19, 17, 15, 13, 12, 14, 16, 18, 20, 2, 4, 6, 8, 10] : Fin 20 → ZMod 23)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
