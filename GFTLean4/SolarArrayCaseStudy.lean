/-
Copyright (c) 2026 Adnan Rashid.
School of Electrical Engineering and Computer Science (SEECS)
National University of Sciences and Technology (NUST)
Islamabad, Pakistan.

Lean 4 formalization accompanying the SBMF 2026 paper:
"Formal Semantics and Machine-Checked Metatheory for
General Fault Trees in Lean 4"
-/

import GFTLean4.GeneralPositive

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.emptyLine false
set_option linter.style.nativeDecide false

/-!
  Case Study: Solar-array mechanical system.

  Based on:
  WU Jianing and YAN Shaoze,
  "Reliability analysis of the solar array based on Fault Tree Analysis",
  Journal of Physics: Conference Series 305 (2011) 012006.

  The file contains:
  1. The hinge subsystem from Figure 6.
  2. The complete mechanical-system fault tree from Figure 3.
-/

namespace GFTree
namespace SolarArray

/-
===========================================================
1. Basic Events for the Hinge Subsystem
===========================================================
-/

inductive HingeEvent where
  | insufficientMainDrivingSpringTorque
  | insufficientBackupDrivingSpringTorque
  | badMaterialCharacteristic
  | badLubricantCharacteristic
  | sealFailure
  | insufficientLockingSpringTorque
  | harshTemperatureEnvironment
  | highFrictionForce
deriving Repr, DecidableEq

abbrev M1 : GFTree HingeEvent :=
  BE HingeEvent.insufficientMainDrivingSpringTorque

abbrev M2 : GFTree HingeEvent :=
  BE HingeEvent.insufficientBackupDrivingSpringTorque

abbrev M3 : GFTree HingeEvent :=
  BE HingeEvent.badMaterialCharacteristic

abbrev M4 : GFTree HingeEvent :=
  BE HingeEvent.badLubricantCharacteristic

abbrev M5 : GFTree HingeEvent :=
  BE HingeEvent.sealFailure

abbrev T6 : GFTree HingeEvent :=
  BE HingeEvent.insufficientLockingSpringTorque

abbrev T7 : GFTree HingeEvent :=
  BE HingeEvent.harshTemperatureEnvironment

abbrev S3 : GFTree HingeEvent :=
  BE HingeEvent.highFrictionForce

/-
===========================================================
2. Intermediate Events from Figure 6
===========================================================
-/

/-- Fault of the main driving spring. -/
abbrev T1 : GFTree HingeEvent :=
  OR [M1, T7]

/-- Fault of the backup driving spring. -/
abbrev T2 : GFTree HingeEvent :=
  OR [M2, T7]

/-- Caging pin cannot insert into the hole. -/
abbrev T3 : GFTree HingeEvent :=
  AND [M3, T7]

/-- Cold welding between the driving bar and the hole. -/
abbrev T4 : GFTree HingeEvent :=
  AND [M4, T7]

/-- Fault of the lubricant. -/
abbrev M6 : GFTree HingeEvent :=
  AND [T7, M4]

/-- Fault of the lubricant/seal branch. -/
abbrev T5 : GFTree HingeEvent :=
  OR [M5, M6]

/-- Fault of the driving spring. -/
abbrev S1 : GFTree HingeEvent :=
  AND [T1, T2]

/-- Fault of the caging pin. -/
abbrev S2 : GFTree HingeEvent :=
  OR [T3, T4, T5]

/-- Fault of the locking spring. -/
abbrev S4 : GFTree HingeEvent :=
  OR [T6, T7]

/-- Deadlocking of the hinge. -/
abbrev F1 : GFTree HingeEvent :=
  OR [S1, S2]

/-- Fault of locking. -/
abbrev F2 : GFTree HingeEvent :=
  OR [S3, S4]

/-- Top event: fault in the hinge. -/
abbrev HingeFailure : GFTree HingeEvent :=
  OR [F1, F2]

/-
===========================================================
3. Structural Verification
===========================================================
-/

/-- The hinge fault tree is well formed. -/
theorem HingeFailure_wellFormed :
    WellFormed HingeFailure := by
  simp [
    HingeFailure,
    F1, F2,
    S1, S2, S3, S4,
    T1, T2, T3, T4, T5, T6, T7,
    M1, M2, M3, M4, M5, M6,
    BE
  ]

/-- The hinge fault tree belongs to the positive fragment. -/
theorem HingeFailure_positive :
    Positive HingeFailure := by
  simp [
    HingeFailure,
    F1, F2,
    S1, S2, S3, S4,
    T1, T2, T3, T4, T5, T6, T7,
    M1, M2, M3, M4, M5, M6,
    OR, AND, BE,
    Positive
  ]

/-- The hinge fault tree is monotone. -/
theorem HingeFailure_monotone :
    Monotone HingeFailure := by
  exact positive_monotone HingeFailure HingeFailure_positive

/-
===========================================================
4. Positive-Tree View
===========================================================
-/

/-- The hinge subsystem as a certified positive fault tree. -/
def HingePositiveTree : PositiveTree HingeEvent :=
  PositiveTree.ofGeneral HingeFailure HingeFailure_positive

/-- The positive-tree view is monotone by the generic theorem. -/
theorem HingePositiveTree_monotone :
    Monotone (HingePositiveTree : GFTree HingeEvent) := by
  exact PositiveTree.monotone HingePositiveTree

/-
===========================================================
5. Executable Semantic Examples
===========================================================
-/

/-- Main driving spring torque alone triggers the main spring branch. -/
theorem M1_triggers_T1 :
    eval ({HingeEvent.insufficientMainDrivingSpringTorque} :
      CutSet HingeEvent) T1 = true := by
  native_decide

/-- Both main and backup driving spring failures trigger S1. -/
theorem M1_M2_trigger_S1 :
    eval ({
      HingeEvent.insufficientMainDrivingSpringTorque,
      HingeEvent.insufficientBackupDrivingSpringTorque
    } : CutSet HingeEvent) S1 = true := by
  native_decide

/-- Main driving spring failure alone does not trigger S1. -/
theorem M1_alone_not_S1 :
    eval ({HingeEvent.insufficientMainDrivingSpringTorque} :
      CutSet HingeEvent) S1 = false := by
  native_decide

/-- Bad material together with harsh temperature triggers T3. -/
theorem M3_T7_trigger_T3 :
    eval ({
      HingeEvent.badMaterialCharacteristic,
      HingeEvent.harshTemperatureEnvironment
    } : CutSet HingeEvent) T3 = true := by
  native_decide

/-- Harsh temperature alone does not trigger T3. -/
theorem T7_alone_not_T3 :
    eval ({HingeEvent.harshTemperatureEnvironment} :
      CutSet HingeEvent) T3 = false := by
  native_decide

/-- High friction directly triggers the locking-fault branch. -/
theorem S3_triggers_F2 :
    eval ({HingeEvent.highFrictionForce} :
      CutSet HingeEvent) F2 = true := by
  native_decide

/-
===========================================================
6. Computed Structural Statistics: Hinge
===========================================================
-/

#eval size HingeFailure
#eval height HingeFailure
#eval gateCount HingeFailure
#eval leafCount HingeFailure
#eval degree HingeFailure
#eval (events HingeFailure).card

/--
Machine-checked structural statistics of the hinge-subsystem
fault tree reported in Table 2 of the paper.
-/
theorem HingeFailure_structural_statistics :
    size HingeFailure = 26 ∧
    height HingeFailure = 6 ∧
    gateCount HingeFailure = 12 ∧
    leafCount HingeFailure = 14 ∧
    degree HingeFailure = 2 ∧
    (events HingeFailure).card = 8 := by
  native_decide

/-
===========================================================
7. Full Solar-Array Mechanical-System Fault Tree
   Figure 3: FTA model of the mechanical system
===========================================================
-/

inductive SolarEvent where
  | G1_batteryEnergyExhaustion
  | G2_photosensorFailure
  | G3_controlSystemFailure
  | G4_electronicArcing
  | G5_cutterFailure
  | G6_manMisoperation
  | G7_tripMechanismDeadlock
  | G8_spaceParticleImpact
  | G9_hingeClearanceVibration
  | G10_solarPanelThermalDeformation
  | G11_disorderedPulseSignal
  | G12_motorMechanicalFailure
  | G13_motorElectronicFailure
  | G14_torsionSpringInsufficientPreload
  | G15_highFrictionCoefficient
  | G16_CCLFracture
  | G17_lockingHoleOutOfShape
  | G18_cagingPinDeformation
  | G19_baffleDeformation
  | G20_baffleFracture
  | G21_harmonicReducerFailure
  | G22_gearFailure
  | G23_hingeDeadlock
  | G24_CCLInsufficientPreload
  | G25_CCLDeformation
  | G26_spaceParticleStructuralFault
  | G27_lubricantFailure
  | G28_cagingPinFracture
  | G29_cagingPinDeformation
  | G30_springInsufficientTorque
  | G31_springFracture
  | G32_cableSlip
  | G33_wheelDeadlock
deriving Repr, DecidableEq

/-
===========================================================
8. Basic Events G1--G33
===========================================================
-/

abbrev SA_G1 : GFTree SolarEvent :=
  BE SolarEvent.G1_batteryEnergyExhaustion
abbrev SA_G2 : GFTree SolarEvent :=
  BE SolarEvent.G2_photosensorFailure
abbrev SA_G3 : GFTree SolarEvent :=
  BE SolarEvent.G3_controlSystemFailure
abbrev SA_G4 : GFTree SolarEvent :=
  BE SolarEvent.G4_electronicArcing
abbrev SA_G5 : GFTree SolarEvent :=
  BE SolarEvent.G5_cutterFailure
abbrev SA_G6 : GFTree SolarEvent :=
  BE SolarEvent.G6_manMisoperation
abbrev SA_G7 : GFTree SolarEvent :=
  BE SolarEvent.G7_tripMechanismDeadlock
abbrev SA_G8 : GFTree SolarEvent :=
  BE SolarEvent.G8_spaceParticleImpact
abbrev SA_G9 : GFTree SolarEvent :=
  BE SolarEvent.G9_hingeClearanceVibration
abbrev SA_G10 : GFTree SolarEvent :=
  BE SolarEvent.G10_solarPanelThermalDeformation
abbrev SA_G11 : GFTree SolarEvent :=
  BE SolarEvent.G11_disorderedPulseSignal
abbrev SA_G12 : GFTree SolarEvent :=
  BE SolarEvent.G12_motorMechanicalFailure
abbrev SA_G13 : GFTree SolarEvent :=
  BE SolarEvent.G13_motorElectronicFailure
abbrev SA_G14 : GFTree SolarEvent :=
  BE SolarEvent.G14_torsionSpringInsufficientPreload
abbrev SA_G15 : GFTree SolarEvent :=
  BE SolarEvent.G15_highFrictionCoefficient
abbrev SA_G16 : GFTree SolarEvent :=
  BE SolarEvent.G16_CCLFracture
abbrev SA_G17 : GFTree SolarEvent :=
  BE SolarEvent.G17_lockingHoleOutOfShape
abbrev SA_G18 : GFTree SolarEvent :=
  BE SolarEvent.G18_cagingPinDeformation
abbrev SA_G19 : GFTree SolarEvent :=
  BE SolarEvent.G19_baffleDeformation
abbrev SA_G20 : GFTree SolarEvent :=
  BE SolarEvent.G20_baffleFracture
abbrev SA_G21 : GFTree SolarEvent :=
  BE SolarEvent.G21_harmonicReducerFailure
abbrev SA_G22 : GFTree SolarEvent :=
  BE SolarEvent.G22_gearFailure
abbrev SA_G23 : GFTree SolarEvent :=
  BE SolarEvent.G23_hingeDeadlock
abbrev SA_G24 : GFTree SolarEvent :=
  BE SolarEvent.G24_CCLInsufficientPreload
abbrev SA_G25 : GFTree SolarEvent :=
  BE SolarEvent.G25_CCLDeformation
abbrev SA_G26 : GFTree SolarEvent :=
  BE SolarEvent.G26_spaceParticleStructuralFault
abbrev SA_G27 : GFTree SolarEvent :=
  BE SolarEvent.G27_lubricantFailure
abbrev SA_G28 : GFTree SolarEvent :=
  BE SolarEvent.G28_cagingPinFracture
abbrev SA_G29 : GFTree SolarEvent :=
  BE SolarEvent.G29_cagingPinDeformation
abbrev SA_G30 : GFTree SolarEvent :=
  BE SolarEvent.G30_springInsufficientTorque
abbrev SA_G31 : GFTree SolarEvent :=
  BE SolarEvent.G31_springFracture
abbrev SA_G32 : GFTree SolarEvent :=
  BE SolarEvent.G32_cableSlip
abbrev SA_G33 : GFTree SolarEvent :=
  BE SolarEvent.G33_wheelDeadlock

/-
===========================================================
9. Published Marker Mapping
===========================================================
-/

abbrev SA_S1 := SA_G1
abbrev SA_S2 := SA_G2
abbrev SA_S3 := SA_G3
abbrev SA_S5 := SA_G4
abbrev SA_S6 := SA_G5
abbrev SA_S7 := SA_G6
abbrev SA_S8 := SA_G7
abbrev SA_S13 := SA_G8
abbrev SA_S14 := SA_G9
abbrev SA_S15 := SA_G10

abbrev SA_T1 := SA_G11
abbrev SA_T2 := SA_G12
abbrev SA_T3 := SA_G13
abbrev SA_T6 := SA_G14
abbrev SA_T9 := SA_G16
abbrev SA_T10 := SA_G17
abbrev SA_T11 := SA_G18
abbrev SA_T14 := SA_G19
abbrev SA_T15 := SA_G20

abbrev SA_M1 := SA_G21
abbrev SA_M2 := SA_G22
abbrev SA_M3 := SA_G23
abbrev SA_M5 := SA_G24
abbrev SA_M6 := SA_G25
abbrev SA_M7 := SA_G26
abbrev SA_M8 := SA_G27
abbrev SA_M9 := SA_G28
abbrev SA_M10 := SA_G29
abbrev SA_M11 := SA_G30
abbrev SA_M12 := SA_G31

abbrev SA_FI1 := SA_G32
abbrev SA_FI2 := SA_G33

/-
===========================================================
10. Intermediate Events
===========================================================
-/

abbrev SA_M4 : GFTree SolarEvent :=
  OR [SA_FI1, SA_FI2]

abbrev SA_T4 : GFTree SolarEvent :=
  OR [SA_M1, SA_M2]

abbrev SA_T5 : GFTree SolarEvent :=
  OR [SA_M3, SA_M4]

abbrev SA_T7 : GFTree SolarEvent :=
  OR [SA_M5, SA_M6]

/-
  Published Table 1 identifies T8 with G15 (high friction
  coefficient), while Figure 3 depicts T8 with descendants
  M7 and M8. We retain both pieces of benchmark information.
-/
abbrev SA_T8 : GFTree SolarEvent :=
  OR [SA_G15, SA_M7, SA_M8]

abbrev SA_T12 : GFTree SolarEvent :=
  OR [SA_M9, SA_M10]

abbrev SA_T13 : GFTree SolarEvent :=
  OR [SA_M11, SA_M12]

abbrev SA_S4 : GFTree SolarEvent :=
  OR [SA_T1, SA_T2, SA_T3, SA_T4]

abbrev SA_S9 : GFTree SolarEvent :=
  OR [SA_T5, SA_T6, SA_T7, SA_T8, SA_T9]

abbrev SA_S10 : GFTree SolarEvent :=
  OR [SA_T10, SA_T11]

abbrev SA_S11 : GFTree SolarEvent :=
  OR [SA_T12, SA_T13]

abbrev SA_S12 : GFTree SolarEvent :=
  OR [SA_T14, SA_T15]

abbrev SA_F1 : GFTree SolarEvent :=
  OR [SA_S1, SA_S2, SA_S3, SA_S4]

abbrev SA_F2 : GFTree SolarEvent :=
  OR [SA_S5, SA_S6, SA_S7]

abbrev SA_F3 : GFTree SolarEvent :=
  OR [SA_S8, SA_S9]

abbrev SA_F4 : GFTree SolarEvent :=
  OR [SA_S10, SA_S11, SA_S12]

abbrev SA_F5 : GFTree SolarEvent :=
  OR [SA_S13, SA_S14, SA_S15]

/-- Top event: failure of the solar array in deployment. -/
abbrev SolarArrayFailure : GFTree SolarEvent :=
  OR [SA_F1, SA_F2, SA_F3, SA_F4, SA_F5]

/-
===========================================================
11. Structural Verification
===========================================================
-/

theorem SolarArrayFailure_wellFormed :
    WellFormed SolarArrayFailure := by
  simp [
    SolarArrayFailure,
    SA_F1, SA_F2, SA_F3, SA_F4, SA_F5,
    SA_S1, SA_S2, SA_S3, SA_S4, SA_S5, SA_S6, SA_S7, SA_S8,
    SA_S9, SA_S10, SA_S11, SA_S12, SA_S13, SA_S14, SA_S15,
    SA_T1, SA_T2, SA_T3, SA_T4, SA_T5, SA_T6, SA_T7, SA_T8,
    SA_T9, SA_T10, SA_T11, SA_T12, SA_T13, SA_T14, SA_T15,
    SA_M1, SA_M2, SA_M3, SA_M4, SA_M5, SA_M6,
    SA_M7, SA_M8, SA_M9, SA_M10, SA_M11, SA_M12,
    SA_FI1, SA_FI2,
    SA_G1, SA_G2, SA_G3, SA_G4, SA_G5, SA_G6, SA_G7, SA_G8,
    SA_G9, SA_G10, SA_G11, SA_G12, SA_G13, SA_G14, SA_G15,
    SA_G16, SA_G17, SA_G18, SA_G19, SA_G20, SA_G21, SA_G22,
    SA_G23, SA_G24, SA_G25, SA_G26, SA_G27, SA_G28, SA_G29,
    SA_G30, SA_G31, SA_G32, SA_G33,
    BE
  ]

theorem SolarArrayFailure_positive :
    Positive SolarArrayFailure := by
  simp [
    SolarArrayFailure,
    SA_F1, SA_F2, SA_F3, SA_F4, SA_F5,
    SA_S1, SA_S2, SA_S3, SA_S4, SA_S5, SA_S6, SA_S7, SA_S8,
    SA_S9, SA_S10, SA_S11, SA_S12, SA_S13, SA_S14, SA_S15,
    SA_T1, SA_T2, SA_T3, SA_T4, SA_T5, SA_T6, SA_T7, SA_T8,
    SA_T9, SA_T10, SA_T11, SA_T12, SA_T13, SA_T14, SA_T15,
    SA_M1, SA_M2, SA_M3, SA_M4, SA_M5, SA_M6,
    SA_M7, SA_M8, SA_M9, SA_M10, SA_M11, SA_M12,
    SA_FI1, SA_FI2,
    SA_G1, SA_G2, SA_G3, SA_G4, SA_G5, SA_G6, SA_G7, SA_G8,
    SA_G9, SA_G10, SA_G11, SA_G12, SA_G13, SA_G14, SA_G15,
    SA_G16, SA_G17, SA_G18, SA_G19, SA_G20, SA_G21, SA_G22,
    SA_G23, SA_G24, SA_G25, SA_G26, SA_G27, SA_G28, SA_G29,
    SA_G30, SA_G31, SA_G32, SA_G33,
    BE
  ]

theorem SolarArrayFailure_monotone :
    Monotone SolarArrayFailure := by
  exact positive_monotone
    SolarArrayFailure
    SolarArrayFailure_positive

/-
===========================================================
12. Positive-Tree View
===========================================================
-/

def SolarArrayPositiveTree : PositiveTree SolarEvent :=
  PositiveTree.ofGeneral
    SolarArrayFailure
    SolarArrayFailure_positive

theorem SolarArrayPositiveTree_monotone :
    Monotone (SolarArrayPositiveTree : GFTree SolarEvent) := by
  exact PositiveTree.monotone SolarArrayPositiveTree

/-
===========================================================
13. Executable Semantic Examples
===========================================================
-/

theorem G1_triggers_SA_F1 :
    eval ({SolarEvent.G1_batteryEnergyExhaustion} :
      CutSet SolarEvent) SA_F1 = true := by
  native_decide

theorem G1_triggers_SolarArrayFailure :
    eval ({SolarEvent.G1_batteryEnergyExhaustion} :
      CutSet SolarEvent) SolarArrayFailure = true := by
  native_decide

theorem G15_triggers_SolarArrayFailure :
    eval ({SolarEvent.G15_highFrictionCoefficient} :
      CutSet SolarEvent) SolarArrayFailure = true := by
  native_decide

theorem G32_triggers_SA_M4 :
    eval ({SolarEvent.G32_cableSlip} :
      CutSet SolarEvent) SA_M4 = true := by
  native_decide

theorem G32_triggers_SolarArrayFailure :
    eval ({SolarEvent.G32_cableSlip} :
      CutSet SolarEvent) SolarArrayFailure = true := by
  native_decide

theorem empty_does_not_trigger_SolarArrayFailure :
    eval (∅ : CutSet SolarEvent)
      SolarArrayFailure = false := by
  native_decide

/-
===========================================================
14. Computed Structural Statistics: Complete Mechanical System
===========================================================
-/

#eval size SolarArrayFailure
#eval height SolarArrayFailure
#eval gateCount SolarArrayFailure
#eval basicEventCount SolarArrayFailure
#eval leafCount SolarArrayFailure
#eval degree SolarArrayFailure
#eval (events SolarArrayFailure).card
#eval events SolarArrayFailure

/--
Machine-checked structural statistics of the complete solar-array
mechanical fault tree reported in Table 2 of the paper.
-/
theorem SolarArrayFailure_structural_statistics :
    size SolarArrayFailure = 51 ∧
    height SolarArrayFailure = 6 ∧
    gateCount SolarArrayFailure = 18 ∧
    leafCount SolarArrayFailure = 33 ∧
    degree SolarArrayFailure = 5 ∧
    (events SolarArrayFailure).card = 33 := by
  native_decide

end SolarArray
end GFTree
