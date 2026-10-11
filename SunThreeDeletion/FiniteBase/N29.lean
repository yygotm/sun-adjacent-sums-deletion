import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_29_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 2
    (![14, 12, 10, 8, 6, 4, 28, 26, 24, 22, 20, 18, 16, 17, 19, 21, 23, 25, 27, 3, 5, 7, 9, 11, 13, 15] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 3
    (![6, 26, 23, 20, 17, 27, 24, 21, 18, 15, 12, 9, 25, 28, 2, 5, 8, 11, 14, 4, 7, 10, 13, 16, 19, 22] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 4
    (![24, 27, 7, 10, 13, 3, 6, 9, 12, 15, 18, 21, 5, 2, 28, 25, 22, 19, 16, 26, 23, 20, 17, 14, 11, 8] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 5
    (![19, 14, 9, 4, 28, 23, 18, 25, 20, 15, 10, 24, 12, 17, 22, 27, 3, 8, 13, 6, 11, 16, 21, 26, 2, 7] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 6
    (![11, 5, 28, 22, 16, 10, 4, 24, 18, 12, 23, 17, 20, 26, 3, 9, 15, 21, 27, 7, 13, 19, 25, 2, 8, 14] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_7 : HasRainbowCycle ({0, 1, 7}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 7
    (![19, 25, 2, 8, 14, 20, 26, 6, 12, 18, 24, 13, 10, 4, 27, 21, 15, 9, 3, 23, 17, 11, 5, 28, 22, 16] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_8 : HasRainbowCycle ({0, 1, 8}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 8
    (![27, 5, 12, 19, 26, 4, 11, 7, 14, 21, 28, 6, 13, 20, 2, 24, 17, 10, 3, 25, 18, 22, 15, 23, 16, 9] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_9 : HasRainbowCycle ({0, 1, 9}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 9
    (![6, 14, 22, 17, 25, 8, 16, 24, 3, 11, 19, 27, 23, 15, 7, 28, 20, 12, 4, 21, 13, 5, 26, 18, 10, 2] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_10 : HasRainbowCycle ({0, 1, 10}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 10
    (![8, 27, 17, 7, 26, 16, 6, 20, 19, 9, 28, 18, 23, 4, 14, 24, 5, 15, 25, 11, 21, 2, 12, 22, 3, 13] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_11 : HasRainbowCycle ({0, 1, 11}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 11
    (![22, 3, 13, 23, 4, 14, 24, 10, 20, 21, 2, 12, 7, 26, 16, 6, 25, 15, 5, 19, 9, 28, 18, 8, 27, 17] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_12 : HasRainbowCycle ({0, 1, 12}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 12
    (![21, 9, 26, 14, 2, 19, 7, 18, 6, 23, 11, 28, 16, 4, 10, 22, 5, 17, 24, 13, 25, 8, 20, 3, 15, 27] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_13 : HasRainbowCycle ({0, 1, 13}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 13
    (![9, 21, 4, 16, 28, 11, 23, 12, 24, 7, 19, 2, 14, 26, 20, 8, 25, 18, 6, 17, 5, 22, 10, 27, 15, 3] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_14 : HasRainbowCycle ({0, 1, 14}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 14
    (![17, 27, 11, 24, 8, 13, 26, 10, 23, 7, 20, 4, 12, 28, 15, 2, 18, 5, 21, 16, 3, 19, 6, 22, 9, 25] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_15 : HasRainbowCycle ({0, 1, 15}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 15
    (![23, 24, 25, 26, 27, 28, 16, 17, 18, 19, 20, 21, 22, 7, 6, 5, 4, 3, 2, 14, 13, 12, 11, 10, 9, 8] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_16 : HasRainbowCycle ({0, 1, 16}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 16
    (![4, 19, 5, 20, 6, 21, 7, 15, 2, 17, 3, 18, 25, 10, 24, 9, 23, 8, 22, 14, 28, 13, 27, 12, 26, 11] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_17 : HasRainbowCycle ({0, 1, 17}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 17
    (![10, 22, 5, 12, 24, 13, 25, 8, 20, 3, 15, 27, 21, 9, 26, 14, 2, 19, 7, 18, 6, 23, 11, 28, 16, 4] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_18 : HasRainbowCycle ({0, 1, 18}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 18
    (![20, 8, 25, 13, 6, 17, 5, 22, 10, 27, 15, 3, 9, 21, 4, 16, 28, 11, 23, 12, 24, 7, 19, 2, 14, 26] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_19 : HasRainbowCycle ({0, 1, 19}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 19
    (![23, 4, 14, 24, 5, 15, 25, 11, 21, 2, 12, 22, 3, 13, 8, 27, 17, 7, 26, 16, 6, 20, 10, 9, 28, 18] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_20 : HasRainbowCycle ({0, 1, 20}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 20
    (![7, 26, 16, 6, 25, 15, 5, 19, 9, 28, 18, 8, 27, 17, 22, 3, 13, 23, 4, 14, 24, 10, 11, 21, 2, 12] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_21 : HasRainbowCycle ({0, 1, 21}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 21
    (![15, 6, 26, 17, 8, 28, 19, 20, 11, 2, 22, 13, 4, 24, 14, 23, 3, 12, 10, 9, 18, 27, 7, 16, 25, 5] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_22 : HasRainbowCycle ({0, 1, 22}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 22
    (![23, 15, 7, 28, 20, 12, 4, 21, 13, 5, 26, 18, 10, 2, 6, 14, 9, 17, 25, 8, 16, 24, 3, 11, 19, 27] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_23 : HasRainbowCycle ({0, 1, 23}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 23
    (![2, 24, 17, 10, 3, 25, 18, 22, 15, 8, 16, 9, 27, 5, 12, 19, 26, 4, 11, 7, 14, 21, 28, 6, 13, 20] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_24 : HasRainbowCycle ({0, 1, 24}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 24
    (![10, 4, 27, 21, 15, 9, 3, 23, 17, 11, 5, 28, 22, 16, 19, 25, 2, 8, 14, 20, 26, 6, 12, 18, 7, 13] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_25 : HasRainbowCycle ({0, 1, 25}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 25
    (![18, 13, 8, 3, 27, 22, 17, 24, 19, 14, 9, 4, 28, 23, 11, 16, 21, 26, 2, 7, 12, 5, 10, 15, 20, 6] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_26 : HasRainbowCycle ({0, 1, 26}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 26
    (![25, 28, 2, 5, 8, 11, 14, 4, 7, 10, 13, 16, 19, 22, 6, 3, 23, 20, 17, 27, 24, 21, 18, 15, 12, 9] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_27 : HasRainbowCycle ({0, 1, 27}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 27
    (![5, 2, 28, 25, 22, 19, 16, 26, 23, 20, 17, 14, 11, 8, 24, 4, 7, 10, 13, 3, 6, 9, 12, 15, 18, 21] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

theorem finite_29_28 : HasRainbowCycle ({0, 1, 28}ᶜ : Set (ZMod 29)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 26) 0 1 28
    (![13, 11, 9, 7, 5, 3, 27, 25, 23, 21, 19, 17, 15, 16, 18, 20, 22, 24, 26, 2, 4, 6, 8, 10, 12, 14] : Fin 26 → ZMod 29)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
