import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_37_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 2
    (![18, 16, 14, 12, 10, 8, 6, 4, 36, 34, 32, 30, 28, 26, 24, 22, 20, 21, 23, 25, 27, 29, 31, 33, 35, 3, 5, 7, 9, 11, 13, 15, 17, 19] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 3
    (![8, 5, 2, 36, 33, 30, 27, 24, 21, 35, 32, 29, 26, 23, 20, 17, 14, 11, 31, 34, 6, 9, 12, 15, 18, 4, 7, 10, 13, 16, 19, 22, 25, 28] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 4
    (![30, 33, 36, 2, 5, 8, 11, 14, 17, 3, 6, 9, 12, 15, 18, 21, 24, 27, 7, 35, 32, 29, 26, 23, 20, 34, 31, 28, 25, 22, 19, 16, 13, 10] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 5
    (![25, 20, 15, 10, 32, 27, 22, 33, 28, 23, 18, 13, 8, 3, 35, 30, 14, 19, 24, 29, 34, 2, 7, 12, 17, 6, 11, 16, 21, 26, 31, 36, 4, 9] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 6
    (![13, 18, 23, 28, 33, 11, 16, 5, 10, 15, 20, 25, 30, 35, 3, 8, 24, 19, 14, 9, 4, 36, 31, 26, 21, 32, 27, 22, 17, 12, 7, 2, 34, 29] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 7
    (![23, 29, 35, 4, 10, 16, 22, 28, 34, 6, 12, 18, 24, 30, 36, 5, 11, 17, 14, 8, 2, 33, 27, 21, 15, 9, 3, 31, 25, 19, 13, 32, 26, 20] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 8
    (![33, 3, 10, 17, 24, 31, 15, 7, 14, 21, 28, 35, 5, 12, 19, 26, 4, 34, 27, 20, 13, 6, 36, 29, 22, 30, 23, 16, 9, 2, 32, 25, 18, 11] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 9
    (![6, 14, 22, 30, 17, 25, 33, 8, 16, 24, 32, 3, 11, 19, 27, 35, 31, 23, 15, 7, 36, 28, 20, 12, 4, 29, 21, 13, 5, 34, 26, 18, 10, 2] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 10
    (![16, 25, 34, 6, 15, 24, 33, 5, 14, 9, 18, 27, 36, 8, 17, 26, 35, 7, 21, 12, 3, 31, 22, 13, 4, 32, 23, 28, 19, 29, 20, 11, 2, 30] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 11
    (![15, 35, 18, 21, 4, 24, 7, 27, 20, 3, 23, 6, 26, 9, 29, 12, 32, 22, 2, 19, 36, 16, 33, 13, 30, 10, 17, 34, 14, 31, 28, 8, 25, 5] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 12
    (![29, 17, 5, 30, 18, 6, 31, 19, 7, 26, 14, 2, 27, 15, 3, 28, 16, 4, 10, 22, 34, 9, 21, 33, 8, 20, 32, 13, 25, 24, 36, 11, 23, 35] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 13
    (![9, 21, 33, 8, 20, 32, 7, 19, 31, 12, 24, 36, 11, 23, 35, 10, 22, 34, 28, 16, 4, 29, 17, 5, 30, 18, 6, 25, 26, 14, 2, 27, 15, 3] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 14
    (![19, 32, 8, 21, 34, 10, 23, 36, 12, 13, 26, 2, 15, 28, 4, 17, 30, 6, 18, 5, 29, 16, 3, 27, 25, 24, 11, 35, 22, 9, 33, 20, 7, 31] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 15
    (![36, 21, 6, 28, 13, 35, 20, 5, 27, 23, 8, 30, 22, 7, 29, 14, 3, 18, 33, 11, 26, 4, 19, 34, 12, 16, 31, 9, 24, 2, 17, 32, 10, 25] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 16
    (![2, 17, 32, 10, 25, 3, 18, 33, 11, 15, 30, 8, 23, 31, 9, 24, 35, 20, 5, 27, 12, 34, 19, 4, 26, 22, 7, 29, 14, 36, 21, 6, 28, 13] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 17
    (![12, 28, 7, 23, 2, 18, 34, 13, 29, 16, 32, 11, 27, 6, 22, 33, 25, 9, 30, 14, 35, 19, 3, 24, 8, 21, 5, 26, 10, 31, 15, 36, 20, 4] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 18
    (![22, 2, 19, 36, 16, 33, 13, 30, 10, 17, 34, 14, 31, 11, 28, 8, 25, 5, 15, 35, 21, 4, 24, 7, 27, 20, 3, 23, 6, 26, 9, 29, 12, 32] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_19 : HasRainbowCycle ({0, 1, 19}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 19
    (![29, 30, 31, 32, 33, 34, 35, 36, 20, 21, 22, 23, 24, 25, 26, 27, 28, 9, 8, 7, 6, 5, 4, 3, 2, 18, 17, 16, 15, 14, 13, 12, 11, 10] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_20 : HasRainbowCycle ({0, 1, 20}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 20
    (![5, 24, 6, 25, 7, 26, 8, 27, 9, 19, 2, 21, 3, 22, 4, 23, 32, 13, 31, 12, 30, 11, 29, 10, 28, 18, 36, 17, 35, 16, 34, 15, 33, 14] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_21 : HasRainbowCycle ({0, 1, 21}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 21
    (![15, 35, 18, 4, 24, 7, 27, 20, 3, 23, 6, 26, 9, 29, 12, 32, 22, 2, 19, 36, 16, 33, 13, 30, 10, 17, 34, 14, 31, 11, 28, 8, 25, 5] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_22 : HasRainbowCycle ({0, 1, 22}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 22
    (![25, 9, 30, 14, 35, 19, 3, 24, 8, 21, 5, 26, 10, 31, 15, 36, 20, 4, 12, 28, 7, 23, 2, 18, 34, 13, 29, 16, 32, 11, 27, 6, 17, 33] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_23 : HasRainbowCycle ({0, 1, 23}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 23
    (![35, 20, 5, 27, 12, 34, 19, 4, 26, 22, 7, 29, 14, 36, 21, 6, 28, 13, 2, 17, 32, 10, 25, 3, 18, 33, 11, 15, 30, 8, 16, 31, 9, 24] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_24 : HasRainbowCycle ({0, 1, 24}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 24
    (![8, 31, 17, 3, 26, 12, 35, 21, 7, 23, 9, 32, 18, 4, 27, 13, 36, 22, 29, 6, 20, 34, 11, 25, 2, 16, 30, 14, 28, 5, 19, 33, 10, 15] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_25 : HasRainbowCycle ({0, 1, 25}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 25
    (![10, 22, 34, 9, 21, 33, 8, 20, 32, 13, 12, 24, 36, 11, 23, 35, 29, 17, 5, 30, 18, 6, 31, 19, 7, 26, 14, 2, 27, 15, 3, 28, 16, 4] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_26 : HasRainbowCycle ({0, 1, 26}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 26
    (![28, 16, 4, 29, 17, 5, 30, 18, 6, 25, 13, 14, 2, 27, 15, 3, 9, 21, 33, 8, 20, 32, 7, 19, 31, 12, 24, 36, 11, 23, 35, 10, 22, 34] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_27 : HasRainbowCycle ({0, 1, 27}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 27
    (![35, 20, 5, 12, 34, 19, 4, 26, 22, 7, 29, 14, 36, 21, 6, 28, 13, 2, 17, 32, 10, 25, 3, 18, 33, 11, 15, 30, 8, 23, 16, 31, 9, 24] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_28 : HasRainbowCycle ({0, 1, 28}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 28
    (![11, 18, 8, 35, 25, 15, 5, 27, 17, 7, 34, 24, 14, 4, 31, 21, 26, 36, 9, 19, 29, 2, 12, 22, 32, 10, 20, 30, 3, 13, 23, 33, 6, 16] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_29 : HasRainbowCycle ({0, 1, 29}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 29
    (![21, 12, 3, 31, 22, 13, 4, 32, 23, 28, 19, 10, 20, 11, 2, 30, 16, 25, 34, 6, 15, 24, 33, 5, 14, 9, 18, 27, 36, 8, 17, 26, 35, 7] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_30 : HasRainbowCycle ({0, 1, 30}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 30
    (![31, 23, 15, 7, 36, 28, 20, 12, 4, 29, 21, 13, 5, 34, 26, 18, 10, 2, 6, 14, 22, 9, 17, 25, 33, 8, 16, 24, 32, 3, 11, 19, 27, 35] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_31 : HasRainbowCycle ({0, 1, 31}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 31
    (![4, 34, 27, 20, 13, 6, 36, 29, 22, 30, 23, 16, 9, 2, 32, 25, 18, 11, 33, 3, 10, 17, 24, 8, 15, 7, 14, 21, 28, 35, 5, 12, 19, 26] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_32 : HasRainbowCycle ({0, 1, 32}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 32
    (![14, 8, 2, 33, 27, 21, 15, 9, 3, 31, 25, 19, 13, 7, 26, 20, 23, 29, 35, 4, 10, 16, 22, 28, 34, 6, 12, 18, 24, 30, 36, 5, 11, 17] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_33 : HasRainbowCycle ({0, 1, 33}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 33
    (![24, 19, 14, 9, 4, 36, 31, 26, 21, 32, 27, 22, 17, 12, 7, 2, 34, 29, 13, 18, 23, 28, 6, 11, 16, 5, 10, 15, 20, 25, 30, 35, 3, 8] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_34 : HasRainbowCycle ({0, 1, 34}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 34
    (![31, 3, 6, 9, 12, 15, 18, 4, 7, 10, 13, 16, 19, 22, 25, 28, 8, 5, 2, 36, 33, 30, 27, 24, 21, 35, 32, 29, 26, 23, 20, 17, 14, 11] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_35 : HasRainbowCycle ({0, 1, 35}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 35
    (![7, 4, 32, 29, 26, 23, 20, 34, 31, 28, 25, 22, 19, 16, 13, 10, 30, 33, 36, 2, 5, 8, 11, 14, 17, 3, 6, 9, 12, 15, 18, 21, 24, 27] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

theorem finite_37_36 : HasRainbowCycle ({0, 1, 36}ᶜ : Set (ZMod 37)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 34) 0 1 36
    (![17, 15, 13, 11, 9, 7, 5, 3, 35, 33, 31, 29, 27, 25, 23, 21, 19, 20, 22, 24, 26, 28, 30, 32, 34, 2, 4, 6, 8, 10, 12, 14, 16, 18] : Fin 34 → ZMod 37)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
