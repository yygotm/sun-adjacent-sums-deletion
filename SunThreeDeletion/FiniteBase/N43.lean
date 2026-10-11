import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_43_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 2
    (![22, 20, 18, 16, 14, 12, 10, 8, 6, 4, 42, 40, 38, 36, 34, 32, 30, 28, 26, 24, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 3
    (![11, 8, 5, 2, 42, 39, 36, 33, 30, 27, 24, 41, 38, 35, 32, 29, 26, 23, 20, 17, 14, 34, 37, 40, 6, 9, 12, 15, 18, 21, 4, 7, 10, 13, 16, 19, 22, 25, 28, 31] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 4
    (![33, 36, 39, 42, 2, 5, 8, 11, 14, 17, 20, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 10, 7, 41, 38, 35, 32, 29, 26, 23, 40, 37, 34, 31, 28, 25, 22, 19, 16, 13] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 5
    (![32, 27, 22, 17, 12, 7, 2, 40, 35, 30, 25, 39, 34, 29, 24, 19, 14, 9, 4, 42, 37, 13, 18, 23, 28, 33, 38, 10, 15, 20, 6, 11, 16, 21, 26, 31, 36, 41, 3, 8] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 6
    (![12, 17, 22, 27, 32, 37, 42, 4, 9, 14, 19, 5, 10, 15, 20, 25, 30, 35, 40, 2, 7, 31, 26, 21, 16, 11, 39, 34, 29, 24, 38, 33, 28, 23, 18, 13, 8, 3, 41, 36] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 7
    (![23, 29, 35, 41, 4, 10, 16, 22, 28, 34, 40, 6, 12, 18, 24, 30, 36, 42, 5, 11, 17, 20, 14, 8, 2, 39, 33, 27, 21, 15, 9, 3, 37, 31, 25, 19, 13, 38, 32, 26] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 8
    (![34, 41, 5, 12, 19, 26, 33, 40, 4, 11, 18, 7, 14, 21, 28, 35, 42, 6, 13, 20, 27, 9, 2, 38, 31, 24, 17, 10, 3, 39, 32, 25, 36, 29, 22, 15, 37, 30, 23, 16] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 9
    (![2, 10, 18, 26, 34, 42, 7, 15, 23, 31, 39, 8, 16, 24, 32, 40, 5, 13, 21, 29, 37, 41, 33, 25, 17, 36, 28, 20, 12, 4, 35, 27, 19, 11, 3, 38, 30, 22, 14, 6] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 10
    (![13, 22, 31, 40, 6, 15, 24, 33, 42, 8, 17, 9, 18, 27, 36, 2, 11, 20, 29, 38, 4, 30, 21, 12, 3, 37, 28, 19, 35, 26, 34, 25, 16, 7, 41, 32, 23, 14, 5, 39] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 11
    (![24, 34, 21, 31, 41, 8, 18, 28, 38, 10, 20, 30, 40, 7, 17, 27, 37, 4, 14, 19, 9, 42, 32, 22, 12, 2, 35, 25, 15, 5, 33, 23, 13, 3, 36, 26, 16, 6, 39, 29] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 12
    (![35, 3, 14, 25, 36, 4, 15, 26, 37, 5, 16, 11, 22, 33, 23, 34, 2, 13, 24, 8, 40, 29, 18, 7, 39, 28, 17, 6, 38, 27, 32, 21, 10, 42, 31, 20, 9, 41, 30, 19] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 13
    (![3, 15, 27, 39, 8, 20, 32, 25, 37, 12, 24, 36, 5, 17, 29, 41, 10, 22, 34, 40, 28, 16, 4, 35, 23, 11, 42, 30, 18, 6, 31, 19, 7, 38, 26, 14, 2, 33, 21, 9] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 14
    (![19, 5, 34, 20, 6, 35, 21, 7, 36, 22, 8, 30, 16, 2, 31, 17, 3, 32, 18, 4, 33, 26, 40, 11, 25, 39, 10, 24, 38, 9, 23, 37, 15, 29, 28, 42, 13, 27, 41, 12] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 15
    (![25, 39, 10, 24, 38, 9, 23, 37, 8, 22, 36, 14, 28, 42, 13, 27, 41, 12, 26, 40, 11, 18, 4, 33, 19, 5, 34, 20, 6, 35, 21, 7, 29, 30, 16, 2, 31, 17, 3, 32] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 16
    (![36, 8, 23, 38, 10, 25, 40, 12, 27, 42, 14, 15, 30, 2, 17, 32, 4, 19, 34, 6, 21, 7, 35, 20, 5, 33, 18, 3, 31, 29, 28, 13, 41, 26, 11, 39, 24, 9, 37, 22] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 17
    (![4, 20, 36, 9, 25, 41, 14, 30, 3, 19, 35, 16, 32, 5, 21, 37, 10, 26, 42, 15, 31, 39, 23, 7, 34, 18, 2, 29, 13, 40, 24, 8, 27, 11, 38, 22, 6, 33, 28, 12] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 18
    (![15, 32, 6, 23, 40, 14, 31, 5, 22, 39, 13, 17, 34, 8, 25, 42, 16, 33, 7, 24, 41, 28, 11, 37, 20, 3, 29, 12, 38, 21, 4, 30, 26, 9, 35, 27, 10, 36, 19, 2] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_19 : HasRainbowCycle ({0, 1, 19}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 19
    (![26, 37, 12, 30, 5, 23, 41, 16, 34, 18, 36, 11, 29, 4, 22, 40, 15, 33, 8, 17, 42, 24, 6, 31, 13, 38, 20, 2, 27, 9, 25, 7, 32, 14, 39, 21, 3, 28, 10, 35] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_20 : HasRainbowCycle ({0, 1, 20}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 20
    (![37, 13, 32, 8, 27, 3, 22, 41, 17, 36, 12, 19, 38, 14, 33, 9, 28, 4, 23, 42, 18, 6, 30, 11, 35, 16, 40, 21, 2, 26, 7, 31, 24, 5, 29, 10, 34, 15, 39, 25] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_21 : HasRainbowCycle ({0, 1, 21}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 21
    (![5, 25, 2, 22, 42, 19, 39, 16, 36, 13, 33, 20, 40, 17, 37, 14, 34, 11, 31, 8, 28, 38, 18, 41, 24, 4, 27, 7, 30, 10, 23, 3, 26, 6, 29, 9, 32, 12, 35, 15] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_22 : HasRainbowCycle ({0, 1, 22}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 22
    (![33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_23 : HasRainbowCycle ({0, 1, 23}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 23
    (![27, 6, 28, 7, 29, 8, 30, 9, 31, 10, 32, 22, 2, 24, 3, 25, 4, 26, 5, 16, 37, 15, 36, 14, 35, 13, 34, 12, 33, 11, 21, 42, 20, 41, 19, 40, 18, 39, 17, 38] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_24 : HasRainbowCycle ({0, 1, 24}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 24
    (![38, 18, 41, 21, 4, 27, 7, 30, 10, 23, 3, 26, 6, 29, 9, 32, 12, 35, 15, 5, 25, 2, 22, 42, 19, 39, 16, 36, 13, 33, 20, 40, 17, 37, 14, 34, 11, 31, 8, 28] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_25 : HasRainbowCycle ({0, 1, 25}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 25
    (![27, 2, 20, 38, 13, 31, 6, 24, 42, 17, 35, 19, 37, 12, 30, 5, 23, 41, 16, 34, 9, 18, 7, 32, 14, 39, 21, 3, 28, 10, 26, 8, 33, 15, 40, 22, 4, 29, 11, 36] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_26 : HasRainbowCycle ({0, 1, 26}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 26
    (![16, 33, 7, 24, 41, 15, 32, 6, 23, 40, 14, 18, 35, 9, 17, 34, 8, 25, 42, 29, 12, 38, 21, 4, 30, 13, 39, 22, 5, 31, 27, 10, 36, 19, 2, 28, 11, 37, 20, 3] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_27 : HasRainbowCycle ({0, 1, 27}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 27
    (![28, 11, 37, 20, 3, 29, 12, 38, 21, 4, 30, 26, 9, 35, 18, 10, 36, 19, 2, 15, 32, 6, 23, 40, 14, 31, 5, 22, 39, 13, 17, 34, 8, 25, 42, 16, 33, 7, 24, 41] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_28 : HasRainbowCycle ({0, 1, 28}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 28
    (![39, 23, 7, 34, 18, 2, 29, 13, 40, 24, 8, 27, 11, 38, 22, 6, 33, 17, 12, 4, 20, 36, 9, 25, 41, 14, 30, 3, 19, 35, 16, 32, 5, 21, 37, 10, 26, 42, 15, 31] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_29 : HasRainbowCycle ({0, 1, 29}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 29
    (![26, 40, 11, 25, 39, 10, 24, 38, 9, 23, 37, 15, 14, 28, 42, 13, 27, 41, 12, 19, 5, 34, 20, 6, 35, 21, 7, 36, 22, 8, 30, 16, 2, 31, 17, 3, 32, 18, 4, 33] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_30 : HasRainbowCycle ({0, 1, 30}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 30
    (![18, 4, 33, 19, 5, 34, 20, 6, 35, 21, 7, 29, 15, 16, 2, 31, 17, 3, 32, 25, 39, 10, 24, 38, 9, 23, 37, 8, 22, 36, 14, 28, 42, 13, 27, 41, 12, 26, 40, 11] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_31 : HasRainbowCycle ({0, 1, 31}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 31
    (![4, 16, 28, 40, 9, 21, 33, 2, 14, 26, 38, 13, 25, 37, 6, 18, 30, 42, 11, 23, 35, 41, 29, 17, 5, 36, 24, 12, 19, 7, 32, 20, 8, 39, 27, 15, 3, 34, 22, 10] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_32 : HasRainbowCycle ({0, 1, 32}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 32
    (![40, 28, 16, 4, 35, 23, 11, 42, 30, 18, 6, 31, 19, 7, 38, 26, 14, 2, 33, 21, 9, 3, 15, 27, 39, 8, 20, 13, 25, 37, 12, 24, 36, 5, 17, 29, 41, 10, 22, 34] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_33 : HasRainbowCycle ({0, 1, 33}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 33
    (![8, 40, 29, 18, 7, 39, 28, 17, 6, 38, 27, 32, 21, 10, 42, 31, 20, 9, 41, 30, 19, 35, 3, 14, 25, 36, 4, 15, 26, 37, 5, 16, 11, 22, 12, 23, 34, 2, 13, 24] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_34 : HasRainbowCycle ({0, 1, 34}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 34
    (![19, 9, 42, 32, 22, 12, 2, 35, 25, 15, 5, 33, 23, 13, 3, 36, 26, 16, 6, 39, 29, 24, 11, 21, 31, 41, 8, 18, 28, 38, 10, 20, 30, 40, 7, 17, 27, 37, 4, 14] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_35 : HasRainbowCycle ({0, 1, 35}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 35
    (![30, 21, 12, 3, 37, 28, 19, 10, 26, 34, 25, 16, 7, 41, 32, 23, 14, 5, 39, 13, 22, 31, 40, 6, 15, 24, 33, 42, 8, 17, 9, 18, 27, 36, 2, 11, 20, 29, 38, 4] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_36 : HasRainbowCycle ({0, 1, 36}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 36
    (![41, 33, 25, 17, 9, 28, 20, 12, 4, 35, 27, 19, 11, 3, 38, 30, 22, 14, 6, 2, 10, 18, 26, 34, 42, 7, 15, 23, 31, 39, 8, 16, 24, 32, 40, 5, 13, 21, 29, 37] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_37 : HasRainbowCycle ({0, 1, 37}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 37
    (![9, 2, 38, 31, 24, 17, 10, 3, 39, 32, 25, 36, 29, 22, 15, 8, 30, 23, 16, 34, 41, 5, 12, 19, 26, 33, 40, 4, 11, 18, 7, 14, 21, 28, 35, 42, 6, 13, 20, 27] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_38 : HasRainbowCycle ({0, 1, 38}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 38
    (![20, 14, 8, 2, 39, 33, 27, 21, 15, 9, 3, 37, 31, 25, 19, 13, 7, 32, 26, 23, 29, 35, 41, 4, 10, 16, 22, 28, 34, 40, 6, 12, 18, 24, 30, 36, 42, 5, 11, 17] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_39 : HasRainbowCycle ({0, 1, 39}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 39
    (![31, 26, 21, 16, 11, 6, 34, 29, 24, 38, 33, 28, 23, 18, 13, 8, 3, 41, 36, 12, 17, 22, 27, 32, 37, 42, 4, 9, 14, 19, 5, 10, 15, 20, 25, 30, 35, 40, 2, 7] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_40 : HasRainbowCycle ({0, 1, 40}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 40
    (![34, 37, 3, 6, 9, 12, 15, 18, 21, 4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 11, 8, 5, 2, 42, 39, 36, 33, 30, 27, 24, 41, 38, 35, 32, 29, 26, 23, 20, 17, 14] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_41 : HasRainbowCycle ({0, 1, 41}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 41
    (![10, 7, 4, 38, 35, 32, 29, 26, 23, 40, 37, 34, 31, 28, 25, 22, 19, 16, 13, 33, 36, 39, 42, 2, 5, 8, 11, 14, 17, 20, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

theorem finite_43_42 : HasRainbowCycle ({0, 1, 42}ᶜ : Set (ZMod 43)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 40) 0 1 42
    (![21, 19, 17, 15, 13, 11, 9, 7, 5, 3, 41, 39, 37, 35, 33, 31, 29, 27, 25, 23, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20] : Fin 40 → ZMod 43)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
