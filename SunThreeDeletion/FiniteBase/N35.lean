import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_35_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 2
    (![18, 16, 14, 12, 10, 8, 6, 4, 34, 32, 30, 28, 26, 24, 22, 20, 19, 21, 23, 25, 27, 29, 31, 33, 3, 5, 7, 9, 11, 13, 15, 17] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 3
    (![9, 6, 32, 29, 26, 23, 20, 33, 30, 27, 24, 21, 18, 15, 12, 28, 31, 34, 2, 5, 8, 11, 14, 17, 4, 7, 10, 13, 16, 19, 22, 25] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 4
    (![27, 30, 33, 7, 10, 13, 16, 3, 6, 9, 12, 15, 18, 21, 24, 8, 5, 2, 34, 31, 28, 25, 22, 19, 32, 29, 26, 23, 20, 17, 14, 11] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 5
    (![14, 15, 16, 17, 18, 19, 20, 21, 22, 6, 7, 8, 9, 10, 11, 12, 13, 31, 30, 29, 28, 27, 26, 25, 24, 23, 4, 3, 2, 34, 33, 32] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 6
    (![17, 11, 5, 34, 28, 22, 16, 10, 4, 30, 24, 18, 12, 29, 23, 20, 26, 32, 3, 9, 15, 21, 27, 33, 7, 13, 19, 25, 31, 2, 8, 14] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 7
    (![19, 25, 31, 2, 8, 14, 20, 26, 32, 6, 12, 18, 24, 30, 13, 16, 10, 4, 33, 27, 21, 15, 9, 3, 29, 23, 17, 11, 5, 34, 28, 22] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 8
    (![34, 26, 18, 10, 2, 29, 21, 13, 5, 28, 20, 12, 4, 31, 23, 15, 7, 3, 11, 19, 27, 16, 24, 32, 9, 17, 25, 33, 6, 14, 22, 30] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 9
    (![2, 10, 18, 26, 34, 7, 15, 23, 31, 8, 16, 24, 32, 5, 13, 21, 29, 33, 25, 17, 28, 20, 12, 4, 27, 19, 11, 3, 30, 22, 14, 6] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 10
    (![11, 20, 29, 3, 12, 21, 30, 4, 13, 9, 18, 27, 19, 28, 2, 24, 15, 6, 32, 23, 14, 5, 31, 22, 26, 17, 8, 34, 25, 16, 7, 33] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 11
    (![7, 31, 20, 9, 33, 22, 24, 25, 14, 3, 27, 16, 5, 29, 18, 30, 6, 17, 28, 4, 15, 26, 2, 13, 12, 23, 34, 10, 21, 32, 8, 19] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 12
    (![33, 21, 9, 32, 20, 8, 31, 19, 7, 24, 23, 11, 34, 22, 10, 4, 16, 28, 5, 17, 29, 6, 18, 30, 13, 25, 2, 14, 26, 3, 15, 27] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 13
    (![3, 15, 27, 4, 16, 28, 5, 17, 29, 12, 24, 25, 2, 14, 26, 32, 20, 8, 31, 19, 7, 30, 18, 6, 23, 11, 34, 22, 10, 33, 21, 9] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 14
    (![23, 24, 25, 26, 27, 28, 29, 30, 31, 15, 16, 17, 18, 19, 20, 21, 22, 5, 4, 3, 2, 34, 33, 32, 13, 12, 11, 10, 9, 8, 7, 6] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 15
    (![24, 25, 26, 27, 28, 29, 30, 31, 32, 16, 17, 18, 19, 20, 21, 22, 23, 6, 5, 4, 3, 2, 34, 33, 14, 13, 12, 11, 10, 9, 8, 7] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 16
    (![32, 19, 3, 22, 6, 25, 9, 20, 4, 23, 7, 26, 10, 29, 13, 5, 21, 2, 18, 34, 15, 31, 12, 28, 17, 33, 14, 30, 11, 27, 8, 24] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 17
    (![4, 20, 33, 14, 30, 11, 27, 16, 32, 13, 29, 10, 26, 7, 23, 31, 15, 34, 18, 2, 21, 5, 24, 8, 19, 3, 22, 6, 25, 9, 28, 12] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 18
    (![27, 28, 29, 30, 31, 32, 33, 34, 19, 20, 21, 22, 23, 24, 25, 26, 9, 8, 7, 6, 5, 4, 3, 2, 17, 16, 15, 14, 13, 12, 11, 10] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_19 : HasRainbowCycle ({0, 1, 19}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 19
    (![22, 5, 23, 6, 24, 7, 25, 8, 26, 18, 2, 20, 3, 21, 4, 13, 30, 12, 29, 11, 28, 10, 27, 9, 17, 34, 16, 33, 15, 32, 14, 31] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_20 : HasRainbowCycle ({0, 1, 20}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 20
    (![31, 15, 34, 18, 2, 21, 5, 24, 8, 19, 3, 22, 6, 25, 9, 28, 12, 4, 17, 33, 14, 30, 11, 27, 16, 32, 13, 29, 10, 26, 7, 23] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_21 : HasRainbowCycle ({0, 1, 21}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 21
    (![30, 31, 32, 33, 34, 2, 3, 22, 23, 24, 25, 26, 27, 28, 29, 12, 11, 10, 9, 8, 7, 6, 5, 4, 20, 19, 18, 17, 16, 15, 14, 13] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_22 : HasRainbowCycle ({0, 1, 22}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 22
    (![31, 32, 33, 34, 2, 3, 4, 23, 24, 25, 26, 27, 28, 29, 30, 13, 12, 11, 10, 9, 8, 7, 6, 5, 21, 20, 19, 18, 17, 16, 15, 14] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_23 : HasRainbowCycle ({0, 1, 23}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 23
    (![4, 16, 28, 5, 17, 29, 6, 18, 30, 13, 25, 2, 14, 26, 3, 15, 27, 33, 21, 9, 32, 20, 8, 31, 19, 7, 24, 12, 11, 34, 22, 10] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_24 : HasRainbowCycle ({0, 1, 24}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 24
    (![32, 20, 8, 31, 19, 7, 30, 18, 6, 23, 11, 34, 22, 10, 33, 21, 9, 3, 15, 27, 4, 16, 28, 5, 17, 29, 12, 13, 25, 2, 14, 26] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_25 : HasRainbowCycle ({0, 1, 25}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 25
    (![6, 30, 19, 8, 32, 21, 10, 34, 23, 24, 13, 2, 26, 15, 4, 28, 17, 29, 5, 16, 27, 3, 14, 12, 11, 22, 33, 9, 20, 31, 7, 18] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_26 : HasRainbowCycle ({0, 1, 26}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 26
    (![12, 21, 30, 4, 13, 22, 31, 5, 14, 10, 19, 28, 2, 11, 20, 29, 3, 25, 16, 7, 33, 24, 15, 6, 32, 23, 27, 18, 9, 17, 8, 34] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_27 : HasRainbowCycle ({0, 1, 27}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 27
    (![24, 15, 6, 32, 23, 14, 5, 31, 22, 26, 17, 8, 34, 25, 16, 7, 33, 11, 20, 29, 3, 12, 21, 30, 4, 13, 9, 18, 10, 19, 28, 2] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_28 : HasRainbowCycle ({0, 1, 28}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 28
    (![33, 25, 17, 9, 20, 12, 4, 27, 19, 11, 3, 30, 22, 14, 6, 2, 10, 18, 26, 34, 7, 15, 23, 31, 8, 16, 24, 32, 5, 13, 21, 29] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_29 : HasRainbowCycle ({0, 1, 29}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 29
    (![20, 26, 32, 3, 9, 15, 21, 27, 33, 7, 13, 19, 25, 31, 2, 8, 14, 17, 11, 5, 34, 28, 22, 16, 10, 4, 30, 24, 18, 12, 6, 23] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_30 : HasRainbowCycle ({0, 1, 30}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 30
    (![16, 10, 4, 33, 27, 21, 15, 9, 3, 29, 23, 17, 11, 5, 34, 28, 22, 19, 25, 31, 2, 8, 14, 20, 26, 32, 6, 12, 18, 24, 7, 13] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_31 : HasRainbowCycle ({0, 1, 31}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 31
    (![5, 6, 7, 8, 9, 10, 11, 12, 13, 32, 33, 34, 2, 3, 4, 22, 21, 20, 19, 18, 17, 16, 15, 14, 30, 29, 28, 27, 26, 25, 24, 23] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_32 : HasRainbowCycle ({0, 1, 32}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 32
    (![28, 31, 34, 2, 5, 8, 11, 14, 17, 4, 7, 10, 13, 16, 19, 22, 25, 9, 6, 3, 29, 26, 23, 20, 33, 30, 27, 24, 21, 18, 15, 12] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_33 : HasRainbowCycle ({0, 1, 33}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 33
    (![8, 5, 2, 34, 31, 28, 25, 22, 19, 32, 29, 26, 23, 20, 17, 14, 11, 27, 30, 4, 7, 10, 13, 16, 3, 6, 9, 12, 15, 18, 21, 24] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

theorem finite_35_34 : HasRainbowCycle ({0, 1, 34}ᶜ : Set (ZMod 35)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 32) 0 1 34
    (![17, 15, 13, 11, 9, 7, 5, 3, 33, 31, 29, 27, 25, 23, 21, 19, 18, 20, 22, 24, 26, 28, 30, 32, 2, 4, 6, 8, 10, 12, 14, 16] : Fin 32 → ZMod 35)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
