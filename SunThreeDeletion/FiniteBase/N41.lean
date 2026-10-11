import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_41_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 2
    (![20, 18, 16, 14, 12, 10, 8, 6, 4, 40, 38, 36, 34, 32, 30, 28, 26, 24, 22, 23, 25, 27, 29, 31, 33, 35, 37, 39, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 3
    (![9, 6, 38, 35, 32, 29, 26, 23, 39, 36, 33, 30, 27, 24, 21, 18, 15, 12, 34, 37, 40, 2, 5, 8, 11, 14, 17, 20, 4, 7, 10, 13, 16, 19, 22, 25, 28, 31] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 4
    (![33, 36, 39, 7, 10, 13, 16, 19, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 8, 5, 2, 40, 37, 34, 31, 28, 25, 22, 38, 35, 32, 29, 26, 23, 20, 17, 14, 11] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 5
    (![28, 23, 18, 13, 8, 3, 39, 34, 29, 24, 37, 32, 27, 22, 17, 12, 7, 2, 38, 33, 15, 20, 25, 30, 35, 40, 4, 9, 14, 19, 6, 11, 16, 21, 26, 31, 36, 10] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 6
    (![14, 19, 24, 29, 34, 39, 3, 8, 13, 18, 5, 10, 15, 20, 25, 30, 35, 40, 4, 9, 27, 22, 17, 12, 7, 2, 38, 33, 28, 23, 36, 31, 26, 21, 16, 11, 37, 32] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 7
    (![25, 31, 37, 2, 8, 14, 20, 26, 32, 38, 6, 12, 18, 24, 30, 36, 13, 19, 16, 10, 4, 39, 33, 27, 21, 15, 9, 3, 35, 29, 23, 17, 11, 5, 40, 34, 28, 22] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 8
    (![36, 2, 9, 16, 23, 30, 37, 3, 10, 17, 7, 14, 21, 28, 35, 15, 22, 29, 5, 39, 32, 25, 18, 11, 4, 38, 31, 24, 34, 27, 20, 13, 6, 40, 33, 26, 19, 12] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 9
    (![6, 14, 22, 30, 38, 5, 13, 21, 29, 37, 8, 16, 24, 32, 40, 7, 15, 23, 31, 39, 35, 27, 19, 11, 3, 36, 28, 20, 12, 4, 33, 25, 17, 34, 26, 18, 10, 2] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 10
    (![17, 26, 35, 3, 12, 21, 30, 39, 7, 16, 9, 18, 27, 36, 4, 13, 22, 31, 40, 8, 24, 15, 6, 38, 29, 20, 11, 2, 34, 25, 32, 23, 14, 5, 37, 28, 19, 33] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 11
    (![28, 38, 7, 17, 27, 37, 6, 16, 26, 36, 10, 20, 30, 40, 9, 19, 29, 39, 8, 18, 13, 3, 34, 24, 14, 4, 35, 25, 15, 5, 31, 21, 32, 22, 12, 2, 33, 23] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 12
    (![39, 9, 20, 31, 23, 34, 4, 15, 11, 22, 33, 3, 14, 25, 36, 6, 17, 28, 2, 32, 21, 10, 40, 29, 18, 7, 37, 26, 30, 19, 8, 38, 27, 16, 5, 35, 24, 13] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 13
    (![9, 21, 33, 4, 16, 28, 40, 11, 23, 35, 12, 24, 36, 7, 19, 31, 2, 14, 26, 38, 32, 20, 8, 37, 25, 30, 18, 6, 29, 17, 5, 34, 22, 10, 39, 27, 15, 3] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 14
    (![11, 38, 24, 10, 37, 23, 9, 36, 22, 8, 28, 27, 13, 40, 26, 12, 39, 25, 32, 5, 19, 33, 6, 20, 34, 7, 21, 35, 15, 29, 2, 16, 30, 3, 17, 31, 4, 18] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 15
    (![31, 4, 18, 32, 5, 19, 33, 6, 20, 34, 14, 28, 29, 2, 16, 30, 3, 17, 10, 37, 23, 9, 36, 22, 8, 35, 21, 7, 27, 13, 40, 26, 12, 39, 25, 11, 38, 24] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 16
    (![30, 14, 39, 23, 7, 32, 25, 9, 26, 10, 35, 19, 3, 28, 12, 37, 21, 5, 13, 29, 4, 20, 36, 11, 27, 2, 18, 34, 17, 33, 8, 24, 40, 15, 31, 6, 22, 38] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 17
    (![12, 28, 3, 19, 35, 10, 26, 33, 16, 32, 7, 23, 39, 14, 30, 5, 21, 37, 29, 13, 38, 22, 6, 31, 15, 40, 24, 8, 25, 9, 34, 18, 2, 27, 11, 36, 20, 4] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 18
    (![8, 31, 13, 36, 23, 5, 28, 10, 24, 6, 29, 11, 34, 16, 39, 21, 3, 26, 35, 12, 30, 7, 25, 2, 20, 38, 15, 33, 19, 37, 14, 32, 9, 27, 4, 22, 40, 17] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_19 : HasRainbowCycle ({0, 1, 19}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 19
    (![34, 11, 29, 6, 24, 37, 14, 32, 18, 36, 13, 31, 8, 26, 3, 21, 39, 16, 7, 30, 12, 35, 17, 40, 22, 4, 27, 9, 23, 5, 28, 10, 33, 15, 38, 20, 2, 25] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_20 : HasRainbowCycle ({0, 1, 20}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 20
    (![4, 23, 39, 17, 36, 14, 33, 11, 19, 38, 16, 35, 13, 32, 10, 29, 7, 26, 37, 18, 40, 21, 2, 24, 5, 27, 8, 30, 22, 3, 25, 6, 28, 9, 31, 12, 34, 15] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_21 : HasRainbowCycle ({0, 1, 21}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 21
    (![32, 33, 34, 35, 36, 37, 38, 39, 40, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 10, 9, 8, 7, 6, 5, 4, 3, 2, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_22 : HasRainbowCycle ({0, 1, 22}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 22
    (![26, 6, 27, 7, 28, 8, 29, 9, 30, 10, 21, 2, 23, 3, 24, 4, 25, 5, 15, 35, 14, 34, 13, 33, 12, 32, 11, 31, 20, 40, 19, 39, 18, 38, 17, 37, 16, 36] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_23 : HasRainbowCycle ({0, 1, 23}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 23
    (![37, 18, 40, 21, 2, 24, 5, 27, 8, 30, 22, 3, 25, 6, 28, 9, 31, 12, 34, 15, 4, 20, 39, 17, 36, 14, 33, 11, 19, 38, 16, 35, 13, 32, 10, 29, 7, 26] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_24 : HasRainbowCycle ({0, 1, 24}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 24
    (![7, 30, 12, 35, 17, 40, 22, 4, 27, 9, 23, 5, 28, 10, 33, 15, 38, 20, 2, 25, 34, 11, 29, 6, 19, 37, 14, 32, 18, 36, 13, 31, 8, 26, 3, 21, 39, 16] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_25 : HasRainbowCycle ({0, 1, 25}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 25
    (![18, 8, 32, 15, 39, 22, 5, 29, 24, 7, 31, 14, 38, 21, 4, 28, 11, 35, 23, 40, 16, 33, 9, 26, 2, 19, 36, 12, 17, 34, 10, 27, 3, 20, 37, 13, 30, 6] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_26 : HasRainbowCycle ({0, 1, 26}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 26
    (![29, 13, 38, 22, 6, 31, 15, 40, 24, 8, 25, 9, 34, 18, 2, 27, 11, 36, 20, 4, 12, 28, 3, 19, 35, 10, 17, 33, 16, 32, 7, 23, 39, 14, 30, 5, 21, 37] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_27 : HasRainbowCycle ({0, 1, 27}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 27
    (![32, 5, 19, 33, 6, 20, 34, 7, 21, 35, 15, 29, 2, 16, 30, 3, 17, 31, 4, 18, 11, 38, 24, 10, 37, 23, 9, 36, 22, 8, 28, 14, 13, 40, 26, 12, 39, 25] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_28 : HasRainbowCycle ({0, 1, 28}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 28
    (![10, 37, 23, 9, 36, 22, 8, 35, 21, 7, 27, 13, 40, 26, 12, 39, 25, 11, 38, 24, 31, 4, 18, 32, 5, 19, 33, 6, 20, 34, 14, 15, 29, 2, 16, 30, 3, 17] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_29 : HasRainbowCycle ({0, 1, 29}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 29
    (![21, 8, 36, 23, 10, 38, 25, 12, 40, 27, 28, 15, 2, 30, 17, 4, 32, 19, 6, 34, 20, 33, 5, 18, 31, 3, 16, 14, 13, 26, 39, 11, 24, 37, 9, 22, 35, 7] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_30 : HasRainbowCycle ({0, 1, 30}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 30
    (![32, 20, 8, 37, 25, 13, 18, 6, 29, 17, 5, 34, 22, 10, 39, 27, 15, 3, 9, 21, 33, 4, 16, 28, 40, 11, 23, 35, 12, 24, 36, 7, 19, 31, 2, 14, 26, 38] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_31 : HasRainbowCycle ({0, 1, 31}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 31
    (![2, 32, 21, 10, 40, 29, 18, 7, 37, 26, 30, 19, 8, 38, 27, 16, 5, 35, 24, 13, 39, 9, 20, 12, 23, 34, 4, 15, 11, 22, 33, 3, 14, 25, 36, 6, 17, 28] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_32 : HasRainbowCycle ({0, 1, 32}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 32
    (![13, 3, 34, 24, 14, 4, 35, 25, 15, 5, 31, 21, 11, 22, 12, 2, 33, 23, 28, 38, 7, 17, 27, 37, 6, 16, 26, 36, 10, 20, 30, 40, 9, 19, 29, 39, 8, 18] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_33 : HasRainbowCycle ({0, 1, 33}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 33
    (![7, 15, 23, 31, 39, 6, 14, 22, 30, 38, 9, 17, 25, 8, 16, 24, 32, 40, 36, 28, 20, 12, 4, 37, 29, 21, 13, 5, 34, 26, 18, 10, 2, 35, 27, 19, 11, 3] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_34 : HasRainbowCycle ({0, 1, 34}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 34
    (![35, 27, 19, 11, 3, 36, 28, 20, 12, 4, 33, 25, 17, 9, 26, 18, 10, 2, 6, 14, 22, 30, 38, 5, 13, 21, 29, 37, 8, 16, 24, 32, 40, 7, 15, 23, 31, 39] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_35 : HasRainbowCycle ({0, 1, 35}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 35
    (![5, 39, 32, 25, 18, 11, 4, 38, 31, 24, 34, 27, 20, 13, 6, 40, 33, 26, 19, 12, 36, 2, 9, 16, 23, 30, 37, 3, 10, 17, 7, 14, 21, 28, 8, 15, 22, 29] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_36 : HasRainbowCycle ({0, 1, 36}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 36
    (![16, 10, 4, 39, 33, 27, 21, 15, 9, 3, 35, 29, 23, 17, 11, 5, 40, 34, 28, 22, 25, 31, 37, 2, 8, 14, 20, 26, 32, 38, 6, 12, 18, 24, 30, 7, 13, 19] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_37 : HasRainbowCycle ({0, 1, 37}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 37
    (![27, 22, 17, 12, 7, 2, 38, 33, 28, 23, 36, 31, 26, 21, 16, 11, 6, 32, 14, 19, 24, 29, 34, 39, 3, 8, 13, 18, 5, 10, 15, 20, 25, 30, 35, 40, 4, 9] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_38 : HasRainbowCycle ({0, 1, 38}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 38
    (![34, 37, 40, 2, 5, 8, 11, 14, 17, 20, 4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 9, 6, 3, 35, 32, 29, 26, 23, 39, 36, 33, 30, 27, 24, 21, 18, 15, 12] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_39 : HasRainbowCycle ({0, 1, 39}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 39
    (![8, 5, 2, 40, 37, 34, 31, 28, 25, 22, 38, 35, 32, 29, 26, 23, 20, 17, 14, 11, 33, 36, 4, 7, 10, 13, 16, 19, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

theorem finite_41_40 : HasRainbowCycle ({0, 1, 40}ᶜ : Set (ZMod 41)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 38) 0 1 40
    (![19, 17, 15, 13, 11, 9, 7, 5, 3, 39, 37, 35, 33, 31, 29, 27, 25, 23, 21, 22, 24, 26, 28, 30, 32, 34, 36, 38, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20] : Fin 38 → ZMod 41)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
