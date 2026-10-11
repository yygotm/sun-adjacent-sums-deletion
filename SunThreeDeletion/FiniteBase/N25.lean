import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_25_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 2
    (![12, 10, 8, 6, 4, 24, 22, 20, 18, 16, 14, 15, 17, 19, 21, 23, 3, 5, 7, 9, 11, 13] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 3
    (![5, 2, 24, 21, 18, 15, 23, 20, 17, 14, 11, 8, 22, 6, 9, 12, 4, 7, 10, 13, 16, 19] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 4
    (![11, 12, 13, 14, 15, 16, 5, 6, 7, 8, 9, 10, 22, 21, 20, 19, 18, 17, 3, 2, 24, 23] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 5
    (![12, 13, 14, 15, 16, 17, 6, 7, 8, 9, 10, 11, 23, 22, 21, 20, 19, 18, 4, 3, 2, 24] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 6
    (![9, 3, 22, 16, 10, 4, 20, 14, 8, 2, 21, 15, 18, 24, 5, 11, 17, 23, 7, 13, 19, 12] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 7
    (![17, 23, 4, 10, 16, 22, 6, 12, 18, 24, 5, 11, 8, 2, 21, 15, 9, 3, 19, 13, 20, 14] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 8
    (![20, 12, 4, 21, 13, 5, 18, 10, 2, 19, 11, 3, 7, 15, 23, 6, 14, 22, 9, 17, 16, 24] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 9
    (![6, 14, 22, 5, 13, 21, 8, 16, 24, 7, 15, 23, 19, 11, 3, 20, 12, 4, 17, 18, 10, 2] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 10
    (![13, 22, 6, 15, 24, 8, 9, 18, 2, 11, 20, 4, 12, 3, 19, 17, 16, 7, 23, 14, 5, 21] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 11
    (![24, 13, 2, 16, 5, 19, 15, 4, 18, 7, 21, 10, 3, 14, 22, 8, 12, 23, 9, 20, 6, 17] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 12
    (![2, 13, 24, 10, 21, 7, 11, 22, 8, 19, 5, 16, 23, 15, 4, 18, 14, 3, 17, 6, 20, 9] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 13
    (![20, 21, 22, 23, 24, 14, 15, 16, 17, 18, 19, 6, 5, 4, 3, 2, 12, 11, 10, 9, 8, 7] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 14
    (![16, 4, 17, 5, 18, 6, 13, 2, 15, 3, 9, 21, 8, 20, 7, 19, 12, 24, 11, 23, 10, 22] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 15
    (![23, 12, 4, 18, 14, 3, 17, 6, 20, 9, 2, 13, 24, 10, 21, 7, 11, 22, 8, 19, 5, 16] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 16
    (![14, 23, 7, 9, 10, 19, 3, 12, 21, 5, 13, 4, 20, 11, 2, 18, 17, 8, 24, 15, 6, 22] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 17
    (![7, 15, 23, 6, 14, 22, 9, 8, 16, 24, 20, 12, 4, 21, 13, 5, 18, 10, 2, 19, 11, 3] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 18
    (![19, 11, 3, 20, 12, 4, 17, 9, 10, 2, 6, 14, 22, 5, 13, 21, 8, 16, 24, 7, 15, 23] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_19 : HasRainbowCycle ({0, 1, 19}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 19
    (![18, 24, 5, 11, 17, 23, 7, 13, 6, 12, 9, 3, 22, 16, 10, 4, 20, 14, 8, 2, 21, 15] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_20 : HasRainbowCycle ({0, 1, 20}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 20
    (![8, 2, 21, 15, 9, 3, 19, 13, 7, 14, 17, 23, 4, 10, 16, 22, 6, 12, 18, 24, 5, 11] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_21 : HasRainbowCycle ({0, 1, 21}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 21
    (![3, 4, 5, 6, 7, 8, 22, 23, 24, 2, 14, 13, 12, 11, 10, 9, 20, 19, 18, 17, 16, 15] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_22 : HasRainbowCycle ({0, 1, 22}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 22
    (![4, 5, 6, 7, 8, 9, 23, 24, 2, 3, 15, 14, 13, 12, 11, 10, 21, 20, 19, 18, 17, 16] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_23 : HasRainbowCycle ({0, 1, 23}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 23
    (![4, 20, 17, 14, 22, 19, 16, 13, 10, 7, 21, 24, 2, 5, 8, 11, 3, 6, 9, 12, 15, 18] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

theorem finite_25_24 : HasRainbowCycle ({0, 1, 24}ᶜ : Set (ZMod 25)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 22) 0 1 24
    (![11, 9, 7, 5, 3, 23, 21, 19, 17, 15, 13, 14, 16, 18, 20, 22, 2, 4, 6, 8, 10, 12] : Fin 22 → ZMod 25)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
