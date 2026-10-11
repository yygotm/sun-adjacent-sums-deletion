import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_31_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 2
    (![16, 14, 12, 10, 8, 6, 4, 30, 28, 26, 24, 22, 20, 18, 17, 19, 21, 23, 25, 27, 29, 3, 5, 7, 9, 11, 13, 15] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 3
    (![8, 5, 2, 30, 27, 24, 21, 18, 29, 26, 23, 20, 17, 14, 11, 25, 28, 6, 9, 12, 15, 4, 7, 10, 13, 16, 19, 22] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 4
    (![24, 27, 30, 2, 5, 8, 11, 14, 3, 6, 9, 12, 15, 18, 21, 7, 29, 26, 23, 20, 17, 28, 25, 22, 19, 16, 13, 10] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 5
    (![13, 14, 15, 16, 17, 18, 19, 20, 6, 7, 8, 9, 10, 11, 12, 28, 27, 26, 25, 24, 23, 22, 21, 4, 3, 2, 30, 29] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 6
    (![9, 14, 19, 24, 29, 3, 8, 13, 5, 10, 15, 20, 25, 30, 4, 22, 17, 12, 7, 2, 28, 23, 18, 26, 21, 16, 11, 27] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 7
    (![17, 23, 29, 4, 10, 16, 22, 28, 6, 12, 18, 24, 30, 5, 11, 14, 8, 2, 27, 21, 15, 9, 3, 25, 19, 13, 26, 20] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 8
    (![25, 15, 22, 29, 5, 12, 7, 14, 21, 28, 4, 11, 18, 6, 30, 23, 16, 9, 2, 26, 19, 24, 17, 10, 3, 27, 20, 13] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 9
    (![2, 10, 18, 26, 3, 11, 19, 27, 8, 16, 24, 17, 25, 29, 21, 13, 5, 28, 20, 12, 4, 23, 15, 7, 30, 22, 14, 6] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 10
    (![14, 4, 25, 15, 5, 26, 16, 6, 22, 12, 2, 23, 13, 3, 24, 19, 29, 8, 18, 28, 7, 17, 27, 11, 21, 20, 30, 9] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 11
    (![18, 28, 7, 17, 27, 6, 16, 26, 10, 20, 30, 9, 19, 29, 8, 13, 3, 24, 14, 4, 25, 15, 5, 21, 22, 12, 2, 23] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 12
    (![26, 6, 17, 28, 8, 19, 30, 10, 11, 22, 2, 13, 24, 4, 15, 5, 25, 14, 3, 23, 21, 20, 9, 29, 18, 7, 27, 16] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 13
    (![3, 15, 27, 8, 20, 25, 12, 24, 5, 17, 29, 10, 22, 28, 16, 4, 23, 11, 30, 18, 6, 19, 7, 26, 14, 2, 21, 9] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 14
    (![11, 24, 6, 19, 27, 9, 13, 26, 8, 21, 3, 16, 29, 20, 7, 25, 12, 30, 17, 4, 22, 18, 5, 23, 10, 28, 15, 2] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 15
    (![19, 2, 16, 30, 13, 27, 10, 24, 14, 28, 11, 25, 8, 22, 5, 12, 29, 18, 4, 21, 7, 17, 3, 20, 6, 23, 9, 26] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 16
    (![24, 25, 26, 27, 28, 29, 30, 17, 18, 19, 20, 21, 22, 23, 8, 7, 6, 5, 4, 3, 2, 15, 14, 13, 12, 11, 10, 9] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 17
    (![4, 20, 5, 21, 6, 22, 7, 23, 16, 2, 18, 3, 19, 27, 11, 26, 10, 25, 9, 24, 8, 15, 30, 14, 29, 13, 28, 12] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 18
    (![12, 29, 15, 4, 21, 7, 17, 3, 20, 6, 23, 9, 26, 19, 2, 16, 30, 13, 27, 10, 24, 14, 28, 11, 25, 8, 22, 5] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_19 : HasRainbowCycle ({0, 1, 19}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 19
    (![20, 7, 25, 12, 30, 17, 4, 22, 18, 5, 23, 10, 28, 15, 2, 11, 24, 6, 14, 27, 9, 13, 26, 8, 21, 3, 16, 29] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_20 : HasRainbowCycle ({0, 1, 20}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 20
    (![28, 16, 4, 23, 11, 30, 18, 6, 19, 7, 26, 14, 2, 21, 9, 3, 15, 27, 8, 13, 25, 12, 24, 5, 17, 29, 10, 22] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_21 : HasRainbowCycle ({0, 1, 21}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 21
    (![19, 29, 8, 18, 28, 7, 17, 27, 11, 10, 20, 30, 9, 14, 4, 25, 15, 5, 26, 16, 6, 22, 12, 2, 23, 13, 3, 24] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_22 : HasRainbowCycle ({0, 1, 22}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 22
    (![13, 3, 24, 14, 4, 25, 15, 5, 21, 11, 12, 2, 23, 18, 28, 7, 17, 27, 6, 16, 26, 10, 20, 30, 9, 19, 29, 8] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_23 : HasRainbowCycle ({0, 1, 23}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 23
    (![3, 11, 19, 27, 4, 12, 20, 28, 9, 17, 25, 2, 10, 18, 26, 30, 22, 14, 6, 29, 21, 13, 5, 24, 16, 8, 15, 7] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_24 : HasRainbowCycle ({0, 1, 24}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 24
    (![29, 21, 13, 5, 28, 20, 12, 4, 23, 15, 7, 30, 22, 14, 6, 2, 10, 18, 26, 3, 11, 19, 27, 8, 16, 9, 17, 25] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_25 : HasRainbowCycle ({0, 1, 25}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 25
    (![18, 24, 30, 5, 11, 17, 23, 29, 7, 13, 19, 6, 12, 15, 9, 3, 28, 22, 16, 10, 4, 26, 20, 14, 8, 2, 27, 21] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_26 : HasRainbowCycle ({0, 1, 26}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 26
    (![14, 8, 2, 27, 21, 15, 9, 3, 25, 19, 13, 7, 20, 17, 23, 29, 4, 10, 16, 22, 28, 6, 12, 18, 24, 30, 5, 11] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_27 : HasRainbowCycle ({0, 1, 27}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 27
    (![4, 5, 6, 7, 8, 9, 10, 11, 28, 29, 30, 2, 3, 19, 18, 17, 16, 15, 14, 13, 12, 26, 25, 24, 23, 22, 21, 20] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_28 : HasRainbowCycle ({0, 1, 28}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 28
    (![25, 3, 6, 9, 12, 15, 4, 7, 10, 13, 16, 19, 22, 8, 5, 2, 30, 27, 24, 21, 18, 29, 26, 23, 20, 17, 14, 11] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_29 : HasRainbowCycle ({0, 1, 29}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 29
    (![7, 4, 26, 23, 20, 17, 28, 25, 22, 19, 16, 13, 10, 24, 27, 30, 2, 5, 8, 11, 14, 3, 6, 9, 12, 15, 18, 21] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

theorem finite_31_30 : HasRainbowCycle ({0, 1, 30}ᶜ : Set (ZMod 31)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 28) 0 1 30
    (![15, 13, 11, 9, 7, 5, 3, 29, 27, 25, 23, 21, 19, 17, 16, 18, 20, 22, 24, 26, 28, 2, 4, 6, 8, 10, 12, 14] : Fin 28 → ZMod 31)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
