import SunThreeDeletion.Certificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SunThreeDeletion
open SunTwoDeletion

theorem finite_7_2 : HasRainbowCycle ({0, 1, 2}ᶜ : Set (ZMod 7)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 4) 0 1 2
    (![4, 6, 5, 3] : Fin 4 → ZMod 7)
    (by decide) (by decide) (by decide)

theorem finite_7_3 : HasRainbowCycle ({0, 1, 3}ᶜ : Set (ZMod 7)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 4) 0 1 3
    (![4, 6, 2, 5] : Fin 4 → ZMod 7)
    (by decide) (by decide) (by decide)

theorem finite_7_4 : HasRainbowCycle ({0, 1, 4}ᶜ : Set (ZMod 7)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 4) 0 1 4
    (![6, 5, 2, 3] : Fin 4 → ZMod 7)
    (by decide) (by decide) (by decide)

theorem finite_7_5 : HasRainbowCycle ({0, 1, 5}ᶜ : Set (ZMod 7)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 4) 0 1 5
    (![4, 6, 2, 3] : Fin 4 → ZMod 7)
    (by decide) (by decide) (by decide)

theorem finite_7_6 : HasRainbowCycle ({0, 1, 6}ᶜ : Set (ZMod 7)) := by
  exact three_cycle_of_certificate (by decide : 2 ≤ 4) 0 1 6
    (![3, 5, 4, 2] : Fin 4 → ZMod 7)
    (by decide) (by decide) (by decide)

end SunThreeDeletion
