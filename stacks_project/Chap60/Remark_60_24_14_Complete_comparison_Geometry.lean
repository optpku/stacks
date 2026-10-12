/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Remark_60_24_14_Complete_comparison_StableBase
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineCompleteStableBase
universe u

namespace CrystallineCompleteStages

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable [IsAdicComplete (Ideal.span {(p : A)}) A]
variable {IA : Ideal A} (γA : DividedPowers IA)
variable (hpI : IsNilpotent (Ideal.Quotient.mk IA (p : A)))
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (e : ℕ)

/-- The actual spectrum of the stable PD quotient maps to the original base. -/
noncomputable def stageBase : Spec (.of (stageRing γA hpI e)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (quotient γA hpI e).toRingHom)

/-- The stage lift uses exponent e plus the stable base offset. -/
noncomputable def stageLift : Scheme.{u} := pullback f (stageBase γA hpI e)

/-- The actual closed immersion of the cofinal stage into Y. -/
noncomputable def stageToY : stageLift γA hpI f e ⟶ Y :=
  pullback.fst f (stageBase γA hpI e)

/-- The smooth stage structure morphism has target the descended PD base. -/
noncomputable def stageToSpec : stageLift γA hpI f e ⟶ Spec (.of (stageRing γA hpI e)) :=
  pullback.snd f (stageBase γA hpI e)

/-- Both routes around the defining stage square coincide. -/
theorem stageToY_comp :
    stageToY γA hpI f e ≫ f = stageToSpec γA hpI f e ≫ stageBase γA hpI e :=
  pullback.condition

/-- Smoothness is base changed to the actual quotient ring, not retained over A. -/
instance stageToSpec_smooth [Smooth f] : Smooth (stageToSpec γA hpI f e) := sorry

/-- Properness is preserved by this base change. -/
instance stageToSpec_isProper [IsProper f] : IsProper (stageToSpec γA hpI f e) := sorry

/-- The map from a stable quotient spectrum to the base is a closed immersion. -/
instance stageBase_isClosedImmersion : IsClosedImmersion (stageBase γA hpI e) := sorry

/-- The stage embedding is a base change of the actual quotient closed immersion. -/
instance stageToY_isClosedImmersion : IsClosedImmersion (stageToY γA hpI f e) := sorry

variable (I : (Spec (.of A)).IdealSheafData) (hI : specIdealEqOfIdealTop IA I)

include hI in
/-- The stable exponent lies in IA, so this particular stage contains the closed fibre. -/
theorem stageToY_ker_le_closedFibre :
    (stageToY γA hpI f e).ker ≤ (smoothLift_inclusion f I).ker := sorry

/-- The closed fibre factors through each cofinal stage via closed-immersion lifting. -/
noncomputable def stageInclusion : smoothLift f I ⟶ stageLift γA hpI f e :=
  IsClosedImmersion.lift (stageToY γA hpI f e) (smoothLift_inclusion f I)
    (stageToY_ker_le_closedFibre γA hpI f e I hI)

/-- The specified factorization recovers the original closed-fibre inclusion. -/
theorem stageInclusion_comp :
    stageInclusion γA hpI f e I hI ≫ stageToY γA hpI f e = smoothLift_inclusion f I := sorry

/-- Consecutive stage schemes are related by the spectrum of the specified PD step. -/
noncomputable def stageStep : stageLift γA hpI f e ⟶ stageLift γA hpI f (e + 1) :=
  pullback.map f (stageBase γA hpI e) f (stageBase γA hpI (e + 1))
    (𝟙 Y) (Spec.map (CommRingCat.ofHom (step γA hpI e).toRingHom))
    (𝟙 (Spec (.of A))) (by simp) (by
      simpa [stageBase, ← Spec.map_comp] using
        congrArg (fun h : A →+* stageRing γA hpI e ↦ Spec.map (CommRingCat.ofHom h))
          (step_comp_quotient γA hpI e).symm)

/-- The stage transition is over the original smooth lift. -/
theorem stageStep_toY : stageStep γA hpI f e ≫ stageToY γA hpI f (e + 1) =
    stageToY γA hpI f e := sorry

/-- Named composition law for the canonical pullback-composition reduction square. -/
theorem stageStepToY : stageStep γA hpI f e ≫ stageToY γA hpI f (e + 1) =
    stageToY γA hpI f e := stageStep_toY γA hpI f e

/-- The fixed closed fibre is compatible with the actual stage transitions. -/
theorem stageInclusion_step : stageInclusion γA hpI f e I hI ≫ stageStep γA hpI f e =
    stageInclusion γA hpI f (e + 1) I hI := sorry

end CrystallineCompleteStages
