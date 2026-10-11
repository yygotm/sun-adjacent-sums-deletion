import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_47_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 2
    (![24, 22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 46, 44, 42, 40, 38, 36, 34, 32, 30, 28, 26, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 3
    (![12, 9, 6, 44, 41, 38, 35, 32, 29, 26, 45, 42, 39, 36, 33, 30, 27, 24, 21, 18, 15, 37, 40, 43, 46, 2, 5, 8, 11, 14, 17, 20, 23, 4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 4
    (![36, 39, 42, 45, 7, 10, 13, 16, 19, 22, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 11, 8, 5, 2, 46, 43, 40, 37, 34, 31, 28, 25, 44, 41, 38, 35, 32, 29, 26, 23, 20, 17, 14] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 5
    (![35, 30, 25, 20, 15, 10, 42, 37, 32, 27, 43, 38, 33, 28, 23, 18, 13, 8, 3, 45, 40, 14, 19, 24, 29, 34, 39, 44, 2, 7, 12, 17, 22, 6, 11, 16, 21, 26, 31, 36, 41, 46, 4, 9] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 6
    (![13, 18, 23, 28, 33, 38, 43, 11, 16, 21, 5, 10, 15, 20, 25, 30, 35, 40, 45, 3, 8, 34, 29, 24, 19, 14, 9, 4, 46, 41, 36, 31, 26, 42, 37, 32, 27, 22, 17, 12, 7, 2, 44, 39] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 7
    (![25, 31, 37, 43, 2, 8, 14, 20, 26, 32, 38, 44, 6, 12, 18, 24, 30, 36, 42, 13, 19, 22, 16, 10, 4, 45, 39, 33, 27, 21, 15, 9, 3, 41, 35, 29, 23, 17, 11, 5, 46, 40, 34, 28] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 8
    (![37, 44, 4, 11, 18, 25, 32, 39, 46, 6, 13, 20, 7, 14, 21, 28, 35, 42, 2, 9, 16, 23, 30, 10, 3, 43, 36, 29, 22, 15, 41, 34, 27, 40, 33, 26, 19, 12, 5, 45, 38, 31, 24, 17] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 9
    (![2, 10, 18, 26, 34, 42, 3, 11, 19, 27, 35, 43, 8, 16, 24, 32, 40, 17, 25, 33, 41, 45, 37, 29, 21, 13, 5, 44, 36, 28, 20, 12, 4, 39, 31, 23, 15, 7, 46, 38, 30, 22, 14, 6] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 10
    (![14, 23, 32, 41, 3, 12, 21, 30, 39, 19, 9, 18, 27, 36, 45, 7, 16, 25, 34, 43, 5, 33, 24, 15, 6, 44, 35, 26, 17, 8, 46, 37, 28, 38, 29, 20, 11, 2, 40, 31, 22, 13, 4, 42] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 11
    (![26, 36, 46, 9, 19, 29, 39, 2, 12, 22, 32, 42, 10, 20, 30, 40, 3, 13, 23, 33, 43, 6, 16, 21, 38, 28, 18, 8, 45, 35, 25, 15, 5, 37, 27, 17, 7, 44, 34, 24, 14, 4, 41, 31] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 12
    (![38, 2, 13, 24, 35, 46, 10, 21, 32, 43, 7, 18, 11, 22, 33, 44, 8, 19, 30, 41, 5, 16, 27, 9, 45, 34, 23, 37, 26, 15, 4, 40, 29, 36, 25, 14, 3, 39, 28, 17, 6, 42, 31, 20] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 13
    (![3, 15, 27, 39, 4, 16, 28, 40, 5, 17, 29, 41, 12, 24, 36, 25, 37, 2, 14, 26, 38, 44, 32, 20, 8, 43, 31, 19, 7, 42, 30, 18, 6, 35, 23, 11, 46, 34, 22, 10, 45, 33, 21, 9] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 14
    (![15, 28, 41, 7, 20, 33, 46, 12, 25, 38, 4, 17, 13, 26, 39, 5, 18, 31, 44, 10, 23, 36, 2, 32, 19, 6, 40, 27, 35, 22, 9, 43, 30, 34, 21, 8, 42, 29, 16, 3, 37, 24, 11, 45] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 15
    (![27, 41, 8, 22, 36, 3, 17, 31, 45, 12, 26, 40, 14, 28, 42, 9, 23, 37, 4, 18, 32, 46, 13, 20, 6, 39, 25, 11, 44, 30, 16, 2, 35, 21, 7, 33, 19, 5, 38, 24, 10, 43, 29, 34] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 16
    (![44, 28, 12, 43, 27, 11, 42, 26, 10, 41, 25, 9, 32, 31, 15, 46, 30, 14, 45, 29, 13, 5, 21, 37, 6, 22, 38, 7, 23, 39, 8, 24, 40, 17, 33, 2, 18, 34, 3, 19, 35, 4, 20, 36] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 17
    (![4, 20, 36, 5, 21, 37, 6, 22, 38, 7, 23, 39, 16, 32, 33, 2, 18, 34, 3, 19, 35, 43, 27, 11, 42, 26, 10, 41, 25, 9, 40, 24, 8, 31, 15, 46, 30, 14, 45, 29, 13, 44, 28, 12] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 18
    (![20, 2, 31, 13, 42, 24, 6, 35, 17, 46, 28, 10, 30, 12, 41, 23, 5, 34, 16, 45, 27, 9, 38, 29, 36, 7, 25, 43, 14, 32, 3, 21, 39, 19, 37, 8, 26, 44, 15, 33, 4, 22, 40, 11] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_19 : HasRainbowCycle ({0, 1, 19}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 19
    (![8, 36, 17, 45, 26, 7, 35, 16, 44, 25, 6, 34, 29, 10, 38, 28, 9, 37, 18, 46, 27, 41, 13, 32, 4, 23, 42, 14, 33, 5, 24, 43, 15, 20, 39, 11, 30, 2, 21, 40, 12, 31, 3, 22] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_20 : HasRainbowCycle ({0, 1, 20}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 20
    (![40, 12, 31, 3, 22, 41, 13, 32, 4, 23, 42, 14, 19, 38, 10, 29, 39, 11, 30, 2, 21, 7, 35, 16, 44, 25, 6, 34, 15, 43, 24, 5, 33, 28, 9, 37, 18, 46, 27, 8, 36, 17, 45, 26] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_21 : HasRainbowCycle ({0, 1, 21}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 21
    (![5, 25, 45, 18, 38, 11, 31, 4, 24, 44, 17, 37, 20, 40, 13, 33, 6, 26, 46, 19, 39, 12, 32, 42, 22, 2, 29, 9, 36, 16, 43, 23, 3, 30, 10, 27, 7, 34, 14, 41, 28, 8, 35, 15] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_22 : HasRainbowCycle ({0, 1, 22}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 22
    (![17, 38, 12, 33, 7, 28, 2, 23, 44, 18, 39, 13, 21, 42, 16, 37, 11, 32, 6, 27, 43, 30, 9, 35, 14, 40, 19, 45, 24, 3, 29, 8, 34, 26, 5, 31, 10, 36, 15, 41, 20, 46, 25, 4] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_23 : HasRainbowCycle ({0, 1, 23}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 23
    (![29, 4, 26, 45, 20, 42, 17, 39, 14, 36, 22, 44, 19, 41, 16, 38, 13, 35, 10, 32, 7, 18, 43, 21, 46, 24, 2, 27, 5, 30, 8, 33, 11, 25, 3, 28, 6, 31, 9, 34, 12, 37, 15, 40] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_24 : HasRainbowCycle ({0, 1, 24}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 24
    (![36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_25 : HasRainbowCycle ({0, 1, 25}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 25
    (![6, 30, 7, 31, 8, 32, 9, 33, 10, 34, 11, 35, 24, 2, 26, 3, 27, 4, 28, 5, 29, 41, 17, 40, 16, 39, 15, 38, 14, 37, 13, 36, 12, 23, 46, 22, 45, 21, 44, 20, 43, 19, 42, 18] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_26 : HasRainbowCycle ({0, 1, 26}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 26
    (![18, 43, 21, 46, 24, 2, 27, 5, 30, 8, 33, 11, 25, 3, 28, 6, 31, 9, 34, 12, 37, 15, 40, 29, 4, 23, 45, 20, 42, 17, 39, 14, 36, 22, 44, 19, 41, 16, 38, 13, 35, 10, 32, 7] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_27 : HasRainbowCycle ({0, 1, 27}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 27
    (![30, 9, 35, 14, 40, 19, 45, 24, 3, 29, 8, 34, 26, 5, 31, 10, 36, 15, 41, 20, 46, 25, 4, 17, 38, 12, 33, 7, 28, 2, 23, 44, 18, 39, 13, 21, 42, 16, 37, 11, 32, 6, 22, 43] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_28 : HasRainbowCycle ({0, 1, 28}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 28
    (![42, 22, 2, 29, 9, 36, 16, 43, 23, 3, 30, 10, 27, 7, 34, 14, 41, 21, 8, 35, 15, 5, 25, 45, 18, 38, 11, 31, 4, 24, 44, 17, 37, 20, 40, 13, 33, 6, 26, 46, 19, 39, 12, 32] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_29 : HasRainbowCycle ({0, 1, 29}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 29
    (![7, 35, 16, 44, 25, 6, 34, 15, 43, 24, 5, 33, 28, 9, 37, 18, 46, 27, 8, 36, 17, 45, 26, 40, 12, 31, 3, 22, 41, 13, 32, 4, 23, 42, 14, 19, 38, 10, 20, 39, 11, 30, 2, 21] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_30 : HasRainbowCycle ({0, 1, 30}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 30
    (![19, 12, 41, 23, 5, 34, 16, 45, 27, 9, 29, 11, 40, 22, 4, 33, 15, 44, 26, 8, 37, 28, 46, 17, 35, 6, 24, 42, 13, 31, 2, 20, 38, 18, 36, 7, 25, 43, 14, 32, 3, 21, 39, 10] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_31 : HasRainbowCycle ({0, 1, 31}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 31
    (![5, 21, 37, 6, 22, 38, 7, 23, 39, 8, 24, 40, 17, 33, 2, 18, 34, 3, 19, 35, 4, 20, 36, 44, 28, 12, 43, 27, 11, 42, 26, 10, 41, 25, 9, 32, 16, 15, 46, 30, 14, 45, 29, 13] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_32 : HasRainbowCycle ({0, 1, 32}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 32
    (![43, 27, 11, 42, 26, 10, 41, 25, 9, 40, 24, 8, 31, 15, 46, 30, 14, 45, 29, 13, 44, 28, 12, 4, 20, 36, 5, 21, 37, 6, 22, 38, 7, 23, 39, 16, 17, 33, 2, 18, 34, 3, 19, 35] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_33 : HasRainbowCycle ({0, 1, 33}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 33
    (![8, 40, 25, 10, 42, 27, 12, 44, 29, 14, 46, 31, 32, 17, 2, 34, 19, 4, 36, 21, 6, 38, 23, 39, 7, 22, 37, 5, 20, 35, 3, 18, 16, 15, 30, 45, 13, 28, 43, 11, 26, 41, 9, 24] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_34 : HasRainbowCycle ({0, 1, 34}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 34
    (![16, 29, 42, 8, 21, 13, 26, 39, 5, 18, 14, 27, 40, 6, 19, 32, 45, 11, 24, 37, 3, 33, 20, 7, 41, 28, 15, 2, 36, 23, 10, 44, 31, 35, 22, 9, 43, 30, 17, 4, 38, 25, 12, 46] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_35 : HasRainbowCycle ({0, 1, 35}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 35
    (![32, 19, 6, 40, 27, 14, 22, 9, 43, 30, 34, 21, 8, 42, 29, 16, 3, 37, 24, 11, 45, 15, 28, 41, 7, 20, 33, 46, 12, 25, 38, 4, 17, 13, 26, 39, 5, 18, 31, 44, 10, 23, 36, 2] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_36 : HasRainbowCycle ({0, 1, 36}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 36
    (![44, 32, 20, 8, 43, 31, 19, 7, 42, 30, 18, 6, 35, 23, 11, 46, 34, 22, 10, 45, 33, 21, 9, 3, 15, 27, 39, 4, 16, 28, 40, 5, 17, 29, 41, 12, 24, 13, 25, 37, 2, 14, 26, 38] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_37 : HasRainbowCycle ({0, 1, 37}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 37
    (![9, 45, 34, 23, 12, 26, 15, 4, 40, 29, 36, 25, 14, 3, 39, 28, 17, 6, 42, 31, 20, 38, 2, 13, 24, 35, 46, 10, 21, 32, 43, 7, 18, 11, 22, 33, 44, 8, 19, 30, 41, 5, 16, 27] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_38 : HasRainbowCycle ({0, 1, 38}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 38
    (![21, 11, 28, 18, 8, 45, 35, 25, 15, 5, 37, 27, 17, 7, 44, 34, 24, 14, 4, 41, 31, 26, 36, 46, 9, 19, 29, 39, 2, 12, 22, 32, 42, 10, 20, 30, 40, 3, 13, 23, 33, 43, 6, 16] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_39 : HasRainbowCycle ({0, 1, 39}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 39
    (![33, 24, 15, 6, 44, 35, 26, 17, 8, 46, 37, 28, 38, 29, 20, 11, 2, 40, 31, 22, 13, 4, 42, 14, 23, 32, 41, 3, 12, 21, 30, 10, 19, 9, 18, 27, 36, 45, 7, 16, 25, 34, 43, 5] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_40 : HasRainbowCycle ({0, 1, 40}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 40
    (![45, 37, 29, 21, 13, 5, 44, 36, 28, 20, 12, 4, 39, 31, 23, 15, 7, 46, 38, 30, 22, 14, 6, 2, 10, 18, 26, 34, 42, 3, 11, 19, 27, 35, 43, 8, 16, 24, 32, 9, 17, 25, 33, 41] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_41 : HasRainbowCycle ({0, 1, 41}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 41
    (![10, 3, 43, 36, 29, 22, 15, 8, 34, 27, 40, 33, 26, 19, 12, 5, 45, 38, 31, 24, 17, 37, 44, 4, 11, 18, 25, 32, 39, 46, 6, 13, 20, 7, 14, 21, 28, 35, 42, 2, 9, 16, 23, 30] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_42 : HasRainbowCycle ({0, 1, 42}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 42
    (![22, 16, 10, 4, 45, 39, 33, 27, 21, 15, 9, 3, 41, 35, 29, 23, 17, 11, 5, 46, 40, 34, 28, 25, 31, 37, 43, 2, 8, 14, 20, 26, 32, 38, 44, 6, 12, 18, 24, 30, 36, 7, 13, 19] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_43 : HasRainbowCycle ({0, 1, 43}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 43
    (![34, 29, 24, 19, 14, 9, 4, 46, 41, 36, 31, 26, 42, 37, 32, 27, 22, 17, 12, 7, 2, 44, 39, 13, 18, 23, 28, 33, 38, 6, 11, 16, 21, 5, 10, 15, 20, 25, 30, 35, 40, 45, 3, 8] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_44 : HasRainbowCycle ({0, 1, 44}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 44
    (![37, 40, 43, 46, 2, 5, 8, 11, 14, 17, 20, 23, 4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, 12, 9, 6, 3, 41, 38, 35, 32, 29, 26, 45, 42, 39, 36, 33, 30, 27, 24, 21, 18, 15] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_45 : HasRainbowCycle ({0, 1, 45}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 45
    (![11, 8, 5, 2, 46, 43, 40, 37, 34, 31, 28, 25, 44, 41, 38, 35, 32, 29, 26, 23, 20, 17, 14, 36, 39, 42, 4, 7, 10, 13, 16, 19, 22, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

theorem finite_47_46 : HasRainbowCycle ({0, 1, 46}ᶜ : Set (ZMod 47)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 44) 0 1 46
    (![23, 21, 19, 17, 15, 13, 11, 9, 7, 5, 3, 45, 43, 41, 39, 37, 35, 33, 31, 29, 27, 25, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22] : Fin 44 → ZMod 47)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
