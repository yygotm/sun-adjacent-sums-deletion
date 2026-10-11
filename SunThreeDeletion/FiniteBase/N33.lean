import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_33_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 2
    (![16, 14, 12, 10, 8, 6, 4, 32, 30, 28, 26, 24, 22, 20, 18, 19, 21, 23, 25, 27, 29, 31, 3, 5, 7, 9, 11, 13, 15, 17] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 3
    (![12, 13, 14, 15, 16, 17, 18, 19, 4, 5, 6, 7, 8, 9, 10, 11, 27, 26, 25, 24, 23, 22, 21, 20, 2, 32, 31, 30, 29, 28] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 4
    (![13, 14, 15, 16, 17, 18, 19, 20, 5, 6, 7, 8, 9, 10, 11, 12, 28, 27, 26, 25, 24, 23, 22, 21, 3, 2, 32, 31, 30, 29] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 5
    (![22, 17, 12, 7, 2, 30, 25, 20, 29, 24, 19, 14, 9, 4, 32, 27, 13, 18, 23, 28, 10, 15, 6, 11, 16, 21, 26, 31, 3, 8] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 6
    (![12, 17, 22, 27, 32, 4, 9, 14, 5, 10, 15, 20, 25, 30, 2, 7, 21, 16, 11, 29, 24, 19, 28, 23, 18, 13, 8, 3, 31, 26] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 7
    (![4, 30, 23, 16, 9, 2, 28, 21, 27, 20, 13, 6, 32, 25, 18, 11, 31, 5, 12, 19, 26, 14, 8, 15, 22, 29, 3, 10, 17, 24] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 8
    (![30, 4, 11, 18, 25, 32, 6, 13, 7, 14, 21, 28, 2, 9, 16, 23, 3, 29, 22, 15, 27, 20, 26, 19, 12, 5, 31, 24, 17, 10] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 9
    (![6, 14, 22, 30, 5, 13, 21, 29, 8, 16, 24, 32, 7, 15, 23, 31, 27, 19, 11, 3, 28, 20, 12, 4, 25, 17, 26, 18, 10, 2] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 10
    (![16, 3, 23, 30, 17, 4, 24, 21, 8, 28, 15, 2, 22, 9, 29, 19, 32, 12, 25, 5, 18, 31, 11, 14, 27, 7, 20, 13, 26, 6] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 11
    (![24, 21, 31, 8, 18, 28, 10, 20, 30, 7, 17, 27, 4, 14, 9, 32, 22, 12, 2, 25, 15, 5, 23, 13, 3, 26, 16, 6, 29, 19] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 12
    (![21, 22, 23, 24, 25, 26, 27, 28, 13, 14, 15, 16, 17, 18, 19, 20, 3, 2, 32, 31, 30, 29, 11, 10, 9, 8, 7, 6, 5, 4] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 13
    (![16, 3, 23, 10, 30, 17, 4, 24, 21, 8, 28, 15, 2, 22, 9, 29, 19, 32, 12, 25, 5, 18, 31, 11, 14, 27, 7, 20, 26, 6] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 14
    (![18, 31, 11, 24, 4, 17, 30, 10, 13, 26, 6, 19, 32, 12, 25, 5, 15, 2, 22, 9, 29, 16, 3, 23, 20, 7, 27, 21, 8, 28] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 15
    (![27, 8, 22, 3, 17, 31, 12, 26, 14, 28, 9, 23, 4, 18, 32, 13, 6, 25, 11, 30, 16, 2, 21, 7, 19, 5, 24, 10, 29, 20] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 16
    (![22, 6, 23, 7, 24, 8, 25, 9, 18, 2, 19, 3, 20, 4, 21, 5, 13, 29, 12, 28, 11, 27, 10, 26, 17, 32, 15, 31, 14, 30] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 17
    (![26, 27, 28, 29, 30, 31, 32, 18, 19, 20, 21, 22, 23, 24, 25, 8, 7, 6, 5, 4, 3, 2, 16, 15, 14, 13, 12, 11, 10, 9] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 18
    (![21, 5, 22, 6, 23, 7, 24, 8, 17, 2, 19, 3, 20, 4, 12, 28, 11, 27, 10, 26, 9, 25, 16, 32, 15, 31, 14, 30, 13, 29] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_19 : HasRainbowCycle ({0, 1, 19}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 19
    (![28, 9, 23, 4, 18, 32, 13, 27, 15, 29, 10, 24, 5, 14, 7, 26, 12, 31, 17, 3, 22, 8, 20, 6, 25, 11, 30, 16, 2, 21] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_20 : HasRainbowCycle ({0, 1, 20}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 20
    (![19, 32, 12, 25, 5, 18, 31, 11, 14, 27, 7, 13, 26, 6, 16, 3, 23, 10, 30, 17, 4, 24, 21, 8, 28, 15, 2, 22, 9, 29] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_21 : HasRainbowCycle ({0, 1, 21}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 21
    (![15, 2, 22, 9, 29, 16, 3, 23, 20, 7, 27, 14, 8, 28, 18, 31, 11, 24, 4, 17, 30, 10, 13, 26, 6, 19, 32, 12, 25, 5] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_22 : HasRainbowCycle ({0, 1, 22}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 22
    (![31, 32, 2, 3, 4, 5, 23, 24, 25, 26, 27, 28, 29, 30, 13, 12, 11, 10, 9, 8, 7, 6, 21, 20, 19, 18, 17, 16, 15, 14] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_23 : HasRainbowCycle ({0, 1, 23}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 23
    (![25, 2, 12, 22, 32, 9, 19, 29, 11, 21, 31, 8, 18, 28, 5, 15, 10, 13, 3, 26, 16, 6, 24, 14, 4, 27, 17, 7, 30, 20] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_24 : HasRainbowCycle ({0, 1, 24}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 24
    (![15, 2, 22, 9, 29, 16, 3, 23, 20, 7, 27, 14, 21, 8, 28, 18, 31, 11, 4, 17, 30, 10, 13, 26, 6, 19, 32, 12, 25, 5] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_25 : HasRainbowCycle ({0, 1, 25}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 25
    (![7, 15, 23, 31, 6, 14, 22, 30, 9, 17, 8, 16, 24, 32, 28, 20, 12, 4, 29, 21, 13, 5, 26, 18, 10, 2, 27, 19, 11, 3] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_26 : HasRainbowCycle ({0, 1, 26}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 26
    (![27, 19, 11, 3, 28, 20, 12, 4, 25, 17, 9, 18, 10, 2, 6, 14, 22, 30, 5, 13, 21, 29, 8, 16, 24, 32, 7, 15, 23, 31] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_27 : HasRainbowCycle ({0, 1, 27}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 27
    (![3, 29, 22, 15, 8, 20, 26, 19, 12, 5, 31, 24, 17, 10, 30, 4, 11, 18, 25, 32, 6, 13, 7, 14, 21, 28, 2, 9, 16, 23] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_28 : HasRainbowCycle ({0, 1, 28}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 28
    (![13, 18, 23, 5, 10, 15, 6, 11, 16, 21, 26, 31, 3, 8, 22, 17, 12, 7, 2, 30, 25, 20, 29, 24, 19, 14, 9, 4, 32, 27] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_29 : HasRainbowCycle ({0, 1, 29}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 29
    (![21, 16, 11, 6, 24, 19, 28, 23, 18, 13, 8, 3, 31, 26, 12, 17, 22, 27, 32, 4, 9, 14, 5, 10, 15, 20, 25, 30, 2, 7] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_30 : HasRainbowCycle ({0, 1, 30}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 30
    (![6, 7, 8, 9, 10, 11, 12, 13, 31, 32, 2, 3, 4, 5, 21, 20, 19, 18, 17, 16, 15, 14, 29, 28, 27, 26, 25, 24, 23, 22] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_31 : HasRainbowCycle ({0, 1, 31}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 31
    (![7, 8, 9, 10, 11, 12, 13, 14, 32, 2, 3, 4, 5, 6, 22, 21, 20, 19, 18, 17, 16, 15, 30, 29, 28, 27, 26, 25, 24, 23] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

theorem finite_33_32 : HasRainbowCycle ({0, 1, 32}ᶜ : Set (ZMod 33)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 30) 0 1 32
    (![15, 13, 11, 9, 7, 5, 3, 31, 29, 27, 25, 23, 21, 19, 17, 18, 20, 22, 24, 26, 28, 30, 2, 4, 6, 8, 10, 12, 14, 16] : Fin 30 → ZMod 33)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
