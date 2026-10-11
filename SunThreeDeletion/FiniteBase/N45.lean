import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_45_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 2
    (![22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 44, 42, 40, 38, 36, 34, 32, 30, 28, 26, 24, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 3
    (![15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 2, 44, 43, 42, 41, 40, 39, 38, 37] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 4
    (![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 3, 2, 44, 43, 42, 41, 40, 39, 38] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 5
    (![17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28, 4, 3, 2, 44, 43, 42, 41, 40, 39] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 6
    (![18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 5, 4, 3, 2, 44, 43, 42, 41, 40] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 7
    (![19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 6, 5, 4, 3, 2, 44, 43, 42, 41] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 8
    (![39, 15, 22, 29, 36, 43, 5, 12, 19, 7, 14, 21, 28, 35, 42, 4, 11, 18, 25, 32, 6, 44, 37, 30, 23, 16, 9, 2, 40, 33, 26, 38, 31, 24, 17, 10, 3, 41, 34, 27, 20, 13] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 9
    (![6, 14, 22, 30, 38, 17, 25, 33, 41, 8, 16, 24, 32, 40, 3, 11, 19, 27, 35, 43, 39, 31, 23, 15, 7, 44, 36, 28, 20, 12, 4, 37, 29, 21, 13, 5, 42, 34, 26, 18, 10, 2] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 10
    (![22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 9, 8, 7, 6, 5, 4, 3, 2, 44] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 11
    (![4, 38, 27, 16, 5, 39, 28, 17, 6, 40, 29, 35, 24, 13, 2, 36, 25, 14, 3, 37, 26, 15, 43, 9, 20, 31, 42, 8, 19, 30, 41, 7, 18, 12, 23, 34, 22, 33, 44, 10, 21, 32] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 12
    (![42, 8, 19, 30, 41, 7, 18, 29, 40, 6, 17, 11, 22, 33, 44, 10, 21, 32, 43, 9, 20, 31, 3, 37, 26, 15, 4, 38, 27, 16, 5, 39, 28, 34, 23, 35, 24, 13, 2, 36, 25, 14] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 13
    (![25, 12, 44, 31, 18, 5, 37, 24, 11, 43, 30, 33, 20, 7, 39, 26, 32, 19, 6, 38, 22, 35, 3, 16, 29, 42, 10, 23, 36, 4, 17, 14, 27, 40, 8, 21, 34, 2, 15, 28, 41, 9] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 14
    (![21, 34, 2, 15, 28, 41, 9, 22, 35, 3, 16, 13, 26, 39, 7, 20, 33, 27, 40, 8, 24, 11, 43, 30, 17, 4, 36, 23, 10, 42, 29, 32, 19, 6, 38, 25, 12, 44, 31, 18, 5, 37] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 15
    (![33, 2, 16, 30, 44, 13, 27, 41, 10, 24, 38, 14, 28, 42, 11, 25, 39, 8, 22, 36, 5, 19, 12, 43, 29, 32, 18, 4, 35, 21, 7, 31, 17, 3, 34, 20, 6, 37, 23, 9, 40, 26] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 16
    (![34, 18, 2, 31, 15, 44, 28, 12, 41, 25, 9, 30, 14, 43, 27, 11, 40, 24, 8, 37, 21, 5, 13, 29, 32, 3, 19, 35, 6, 22, 38, 17, 33, 4, 20, 36, 7, 23, 39, 10, 26, 42] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 17
    (![12, 28, 44, 15, 31, 2, 18, 34, 5, 21, 37, 16, 32, 3, 19, 35, 6, 22, 38, 9, 25, 41, 33, 30, 14, 43, 27, 11, 40, 24, 8, 29, 13, 42, 26, 10, 39, 23, 7, 36, 20, 4] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 18
    (![24, 41, 13, 30, 2, 19, 36, 8, 25, 42, 14, 17, 34, 6, 23, 40, 12, 29, 35, 7, 21, 4, 32, 15, 43, 26, 9, 37, 20, 3, 31, 28, 11, 39, 22, 5, 33, 16, 44, 27, 10, 38] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_19 : HasRainbowCycle ({0, 1, 19}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 19
    (![43, 24, 5, 31, 12, 38, 26, 7, 33, 27, 8, 34, 15, 41, 22, 3, 29, 10, 36, 17, 4, 23, 42, 16, 35, 9, 28, 2, 21, 40, 14, 20, 39, 13, 32, 6, 25, 44, 18, 37, 11, 30] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_20 : HasRainbowCycle ({0, 1, 20}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 20
    (![3, 22, 41, 15, 34, 8, 27, 39, 13, 19, 38, 12, 31, 5, 24, 43, 17, 36, 10, 29, 42, 23, 4, 30, 11, 37, 18, 44, 25, 6, 32, 26, 7, 33, 14, 40, 21, 2, 28, 9, 35, 16] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_21 : HasRainbowCycle ({0, 1, 21}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 21
    (![33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 9, 8, 7, 6, 5, 4, 3, 2, 44, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_22 : HasRainbowCycle ({0, 1, 22}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 22
    (![7, 30, 8, 31, 9, 32, 10, 33, 11, 34, 12, 24, 2, 25, 3, 26, 4, 27, 5, 28, 6, 29, 40, 17, 39, 16, 38, 15, 37, 14, 36, 13, 35, 23, 44, 21, 43, 20, 42, 19, 41, 18] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_23 : HasRainbowCycle ({0, 1, 23}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 23
    (![35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_24 : HasRainbowCycle ({0, 1, 24}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 24
    (![6, 29, 7, 30, 8, 31, 9, 32, 10, 33, 11, 23, 2, 25, 3, 26, 4, 27, 5, 28, 39, 16, 38, 15, 37, 14, 36, 13, 35, 12, 34, 22, 44, 21, 43, 20, 42, 19, 41, 18, 40, 17] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_25 : HasRainbowCycle ({0, 1, 25}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 25
    (![37, 38, 39, 40, 41, 42, 43, 44, 2, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_26 : HasRainbowCycle ({0, 1, 26}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 26
    (![4, 23, 42, 16, 35, 9, 28, 2, 21, 40, 14, 20, 39, 13, 32, 6, 25, 44, 18, 37, 11, 30, 43, 24, 5, 31, 12, 38, 19, 7, 33, 27, 8, 34, 15, 41, 22, 3, 29, 10, 36, 17] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_27 : HasRainbowCycle ({0, 1, 27}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 27
    (![42, 23, 4, 30, 11, 37, 18, 44, 25, 6, 32, 26, 7, 33, 14, 40, 21, 2, 28, 9, 35, 16, 3, 22, 41, 15, 34, 8, 20, 39, 13, 19, 38, 12, 31, 5, 24, 43, 17, 36, 10, 29] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_28 : HasRainbowCycle ({0, 1, 28}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 28
    (![25, 42, 14, 31, 3, 20, 37, 9, 26, 43, 15, 18, 35, 7, 24, 41, 13, 30, 2, 19, 36, 8, 22, 5, 33, 16, 44, 27, 10, 38, 21, 4, 32, 29, 12, 40, 23, 6, 34, 17, 11, 39] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_29 : HasRainbowCycle ({0, 1, 29}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 29
    (![21, 4, 32, 15, 43, 26, 9, 37, 20, 3, 31, 28, 11, 39, 22, 5, 33, 16, 44, 27, 10, 38, 24, 41, 13, 30, 2, 19, 36, 8, 25, 42, 14, 17, 34, 6, 23, 40, 12, 18, 35, 7] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_30 : HasRainbowCycle ({0, 1, 30}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 30
    (![33, 17, 14, 43, 27, 11, 40, 24, 8, 29, 13, 42, 26, 10, 39, 23, 7, 36, 20, 4, 12, 28, 44, 15, 31, 2, 18, 34, 5, 21, 37, 16, 32, 3, 19, 35, 6, 22, 38, 9, 25, 41] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_31 : HasRainbowCycle ({0, 1, 31}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 31
    (![34, 3, 17, 14, 28, 42, 11, 25, 39, 15, 29, 43, 12, 26, 40, 9, 23, 37, 6, 20, 13, 44, 30, 16, 2, 33, 19, 5, 36, 22, 8, 32, 18, 4, 35, 21, 7, 38, 24, 10, 41, 27] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_32 : HasRainbowCycle ({0, 1, 32}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 32
    (![12, 43, 29, 15, 18, 4, 35, 21, 7, 31, 17, 3, 34, 20, 6, 37, 23, 9, 40, 26, 33, 2, 16, 30, 44, 13, 27, 41, 10, 24, 38, 14, 28, 42, 11, 25, 39, 8, 22, 36, 5, 19] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_33 : HasRainbowCycle ({0, 1, 33}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 33
    (![24, 11, 43, 30, 17, 4, 36, 23, 10, 42, 29, 32, 19, 6, 38, 25, 12, 44, 31, 18, 5, 37, 21, 34, 2, 15, 28, 41, 9, 22, 35, 3, 16, 13, 26, 39, 7, 20, 14, 27, 40, 8] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_34 : HasRainbowCycle ({0, 1, 34}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 34
    (![43, 9, 20, 31, 42, 8, 19, 30, 41, 7, 18, 12, 23, 11, 22, 33, 44, 10, 21, 32, 4, 38, 27, 16, 5, 39, 28, 17, 6, 40, 29, 35, 24, 13, 2, 36, 25, 14, 3, 37, 26, 15] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_35 : HasRainbowCycle ({0, 1, 35}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 35
    (![3, 37, 26, 15, 4, 38, 27, 16, 5, 39, 28, 34, 23, 12, 24, 13, 2, 36, 25, 14, 42, 8, 19, 30, 41, 7, 18, 29, 40, 6, 17, 11, 22, 33, 44, 10, 21, 32, 43, 9, 20, 31] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_36 : HasRainbowCycle ({0, 1, 36}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 36
    (![3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 37, 38, 39, 40, 41, 42, 43, 44, 2, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_37 : HasRainbowCycle ({0, 1, 37}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 37
    (![7, 15, 23, 31, 39, 2, 10, 18, 26, 34, 42, 9, 17, 25, 33, 41, 4, 12, 20, 28, 36, 44, 40, 32, 24, 16, 8, 29, 21, 13, 5, 38, 30, 22, 14, 6, 43, 35, 27, 19, 11, 3] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_38 : HasRainbowCycle ({0, 1, 38}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 38
    (![39, 31, 23, 15, 7, 44, 36, 28, 20, 12, 4, 37, 29, 21, 13, 5, 42, 34, 26, 18, 10, 2, 6, 14, 22, 30, 9, 17, 25, 33, 41, 8, 16, 24, 32, 40, 3, 11, 19, 27, 35, 43] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_39 : HasRainbowCycle ({0, 1, 39}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 39
    (![6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 40, 41, 42, 43, 44, 2, 3, 4, 5, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29, 28] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_40 : HasRainbowCycle ({0, 1, 40}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 40
    (![7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 41, 42, 43, 44, 2, 3, 4, 5, 6, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30, 29] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_41 : HasRainbowCycle ({0, 1, 41}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 41
    (![8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 42, 43, 44, 2, 3, 4, 5, 6, 7, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31, 30] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_42 : HasRainbowCycle ({0, 1, 42}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 42
    (![9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 43, 44, 2, 3, 4, 5, 6, 7, 8, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 31] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_43 : HasRainbowCycle ({0, 1, 43}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 43
    (![10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 44, 2, 3, 4, 5, 6, 7, 8, 9, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

theorem finite_45_44 : HasRainbowCycle ({0, 1, 44}ᶜ : Set (ZMod 45)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 42) 0 1 44
    (![21, 19, 17, 15, 13, 11, 9, 7, 5, 3, 43, 41, 39, 37, 35, 33, 31, 29, 27, 25, 23, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22] : Fin 42 → ZMod 45)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
