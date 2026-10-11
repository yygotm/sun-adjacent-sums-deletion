import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_39_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 2
    (![20, 18, 16, 14, 12, 10, 8, 6, 4, 38, 36, 34, 32, 30, 28, 26, 24, 22, 21, 23, 25, 27, 29, 31, 33, 35, 37, 3, 5, 7, 9, 11, 13, 15, 17, 19] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 3
    (![13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 4, 5, 6, 7, 8, 9, 10, 11, 12, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 2, 38, 37, 36, 35, 34, 33] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 4
    (![14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 5, 6, 7, 8, 9, 10, 11, 12, 13, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 3, 2, 38, 37, 36, 35, 34] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 5
    (![29, 24, 19, 14, 9, 4, 38, 33, 28, 23, 35, 30, 25, 20, 15, 10, 34, 12, 17, 22, 27, 32, 37, 3, 8, 13, 18, 6, 11, 16, 21, 26, 31, 36, 2, 7] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 6
    (![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 7, 8, 9, 10, 11, 12, 13, 14, 15, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 5, 4, 3, 2, 38, 37, 36] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 7
    (![9, 2, 34, 27, 20, 13, 6, 38, 31, 24, 33, 26, 19, 12, 5, 37, 30, 23, 16, 32, 14, 21, 28, 35, 3, 10, 17, 8, 15, 22, 29, 36, 4, 11, 18, 25] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 8
    (![38, 30, 22, 14, 6, 37, 29, 21, 13, 5, 32, 24, 16, 31, 23, 15, 7, 3, 11, 19, 27, 35, 4, 12, 20, 28, 36, 9, 17, 25, 33, 2, 10, 18, 26, 34] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 9
    (![2, 10, 18, 26, 34, 3, 11, 19, 27, 35, 8, 16, 24, 32, 17, 25, 33, 37, 29, 21, 13, 5, 36, 28, 20, 12, 4, 31, 23, 15, 7, 38, 30, 22, 14, 6] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 10
    (![18, 8, 37, 27, 17, 7, 36, 26, 16, 6, 30, 20, 29, 19, 9, 38, 28, 23, 33, 4, 14, 24, 34, 5, 15, 25, 35, 11, 21, 31, 2, 12, 22, 32, 3, 13] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 11
    (![22, 32, 3, 13, 23, 33, 4, 14, 24, 34, 10, 20, 30, 21, 31, 2, 12, 17, 7, 36, 26, 16, 6, 35, 25, 15, 5, 29, 19, 9, 38, 28, 18, 8, 37, 27] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 12
    (![32, 4, 15, 26, 37, 9, 20, 31, 3, 14, 11, 22, 33, 5, 16, 27, 38, 10, 21, 7, 35, 24, 13, 2, 30, 19, 8, 36, 25, 28, 17, 6, 34, 23, 29, 18] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 13
    (![23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 14, 15, 16, 17, 18, 19, 20, 21, 22, 3, 2, 38, 37, 36, 35, 34, 33, 12, 11, 10, 9, 8, 7, 6, 5, 4] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 14
    (![17, 3, 28, 25, 11, 36, 22, 8, 26, 12, 37, 23, 9, 34, 20, 6, 31, 24, 38, 13, 27, 2, 16, 30, 5, 19, 33, 15, 29, 4, 18, 32, 7, 21, 35, 10] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 15
    (![23, 37, 12, 26, 29, 4, 18, 32, 14, 28, 3, 17, 31, 6, 20, 34, 9, 16, 2, 27, 13, 38, 24, 10, 35, 21, 7, 25, 11, 36, 22, 8, 33, 19, 5, 30] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 16
    (![36, 20, 4, 27, 11, 34, 18, 2, 25, 9, 24, 8, 31, 15, 38, 22, 6, 29, 13, 5, 21, 37, 14, 30, 7, 23, 32, 17, 33, 10, 26, 3, 19, 35, 12, 28] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 17
    (![4, 20, 36, 13, 29, 6, 22, 38, 15, 31, 16, 32, 9, 25, 2, 18, 34, 11, 27, 35, 19, 3, 26, 10, 33, 24, 8, 23, 7, 30, 14, 37, 21, 5, 28, 12] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 18
    (![14, 31, 9, 26, 4, 21, 38, 16, 33, 11, 17, 34, 12, 29, 7, 24, 2, 19, 36, 25, 8, 30, 13, 35, 23, 6, 28, 22, 5, 27, 10, 32, 15, 37, 20, 3] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_19 : HasRainbowCycle ({0, 1, 19}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 19
    (![6, 26, 7, 27, 8, 28, 9, 29, 10, 30, 21, 2, 22, 3, 23, 4, 24, 5, 25, 35, 15, 34, 14, 33, 13, 32, 12, 31, 11, 20, 38, 18, 37, 17, 36, 16] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_20 : HasRainbowCycle ({0, 1, 20}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 20
    (![30, 31, 32, 33, 34, 35, 36, 37, 38, 21, 22, 23, 24, 25, 26, 27, 28, 29, 10, 9, 8, 7, 6, 5, 4, 3, 2, 19, 18, 17, 16, 15, 14, 13, 12, 11] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_21 : HasRainbowCycle ({0, 1, 21}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 21
    (![5, 25, 6, 26, 7, 27, 8, 28, 9, 29, 20, 2, 22, 3, 23, 4, 24, 34, 14, 33, 13, 32, 12, 31, 11, 30, 10, 19, 38, 18, 37, 17, 36, 16, 35, 15] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_22 : HasRainbowCycle ({0, 1, 22}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 22
    (![15, 32, 10, 27, 5, 17, 34, 12, 18, 35, 13, 30, 8, 25, 3, 20, 37, 26, 9, 31, 14, 36, 19, 2, 24, 7, 29, 23, 6, 28, 11, 33, 16, 38, 21, 4] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_23 : HasRainbowCycle ({0, 1, 23}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 23
    (![25, 8, 30, 13, 35, 18, 6, 28, 22, 5, 27, 10, 32, 15, 37, 20, 3, 14, 31, 9, 26, 4, 21, 38, 16, 33, 11, 17, 34, 12, 29, 7, 24, 2, 19, 36] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_24 : HasRainbowCycle ({0, 1, 24}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 24
    (![35, 19, 3, 26, 10, 33, 17, 8, 23, 7, 30, 14, 37, 21, 5, 28, 12, 4, 20, 36, 13, 29, 6, 22, 38, 15, 31, 16, 32, 9, 25, 2, 18, 34, 11, 27] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_25 : HasRainbowCycle ({0, 1, 25}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 25
    (![24, 38, 13, 27, 2, 16, 30, 5, 19, 33, 15, 29, 4, 18, 32, 7, 21, 35, 10, 17, 3, 28, 14, 11, 36, 22, 8, 26, 12, 37, 23, 9, 34, 20, 6, 31] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_26 : HasRainbowCycle ({0, 1, 26}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 26
    (![16, 2, 27, 13, 38, 24, 10, 35, 21, 7, 25, 11, 36, 22, 8, 33, 19, 5, 30, 23, 37, 12, 15, 29, 4, 18, 32, 14, 28, 3, 17, 31, 6, 20, 34, 9] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_27 : HasRainbowCycle ({0, 1, 27}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 27
    (![37, 38, 2, 3, 4, 5, 6, 7, 28, 29, 30, 31, 32, 33, 34, 35, 36, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 26, 25, 24, 23, 22, 21, 20, 19, 18] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_28 : HasRainbowCycle ({0, 1, 28}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 28
    (![33, 5, 16, 27, 38, 10, 21, 32, 4, 15, 12, 23, 34, 6, 17, 11, 22, 8, 36, 25, 14, 3, 31, 20, 9, 37, 26, 29, 18, 7, 35, 24, 13, 2, 30, 19] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_29 : HasRainbowCycle ({0, 1, 29}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 29
    (![7, 35, 24, 13, 2, 30, 19, 8, 36, 25, 28, 17, 6, 34, 23, 12, 18, 32, 4, 15, 26, 37, 9, 20, 31, 3, 14, 11, 22, 33, 5, 16, 27, 38, 10, 21] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_30 : HasRainbowCycle ({0, 1, 30}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 30
    (![17, 7, 36, 26, 16, 6, 35, 25, 15, 5, 29, 19, 9, 38, 28, 18, 8, 37, 27, 22, 32, 3, 13, 23, 33, 4, 14, 24, 34, 10, 20, 11, 21, 31, 2, 12] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_31 : HasRainbowCycle ({0, 1, 31}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 31
    (![3, 11, 19, 27, 35, 4, 12, 20, 28, 36, 9, 17, 25, 33, 2, 10, 18, 26, 34, 38, 30, 22, 14, 6, 37, 29, 21, 13, 5, 32, 24, 16, 8, 23, 15, 7] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_32 : HasRainbowCycle ({0, 1, 32}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 32
    (![37, 29, 21, 13, 5, 36, 28, 20, 12, 4, 31, 23, 15, 7, 38, 30, 22, 14, 6, 2, 10, 18, 26, 34, 3, 11, 19, 27, 35, 8, 16, 24, 9, 17, 25, 33] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_33 : HasRainbowCycle ({0, 1, 33}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 33
    (![8, 26, 19, 12, 5, 37, 30, 23, 32, 25, 18, 11, 4, 36, 29, 22, 15, 31, 38, 6, 13, 20, 27, 34, 2, 9, 16, 7, 14, 21, 28, 35, 3, 10, 17, 24] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_34 : HasRainbowCycle ({0, 1, 34}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 34
    (![5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 35, 36, 37, 38, 2, 3, 4, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 33, 32, 31, 30, 29, 28, 27, 26, 25] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_35 : HasRainbowCycle ({0, 1, 35}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 35
    (![28, 23, 18, 13, 8, 3, 37, 32, 27, 22, 34, 29, 24, 19, 14, 9, 4, 38, 33, 11, 16, 21, 26, 31, 36, 2, 7, 12, 17, 5, 10, 15, 20, 25, 30, 6] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_36 : HasRainbowCycle ({0, 1, 36}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 36
    (![7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 37, 38, 2, 3, 4, 5, 6, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 35, 34, 33, 32, 31, 30, 29, 28, 27] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_37 : HasRainbowCycle ({0, 1, 37}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 37
    (![8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 38, 2, 3, 4, 5, 6, 7, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 36, 35, 34, 33, 32, 31, 30, 29, 28] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

theorem finite_39_38 : HasRainbowCycle ({0, 1, 38}ᶜ : Set (ZMod 39)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 36) 0 1 38
    (![19, 17, 15, 13, 11, 9, 7, 5, 3, 37, 35, 33, 31, 29, 27, 25, 23, 21, 20, 22, 24, 26, 28, 30, 32, 34, 36, 2, 4, 6, 8, 10, 12, 14, 16, 18] : Fin 36 → ZMod 39)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
