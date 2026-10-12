/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback.LineBundle
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.TensorSplitting
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.TensorSplitting.FirstProjection

/-!
# Chow pullback along the first projection of a tensor-section splitting

This file records the bijectivity and injectivity of the flat pullback from
the base zero scheme to the first factor zero scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.TensorSectionSplitting

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable (delta : S → ℤ) [IsDimensionFunction delta]
variable (Y : Over S) [LocallyOfFiniteType Y.hom]
variable {L₁ L₂ : Y.left.Modules}
variable [Scheme.Modules.Invertible L₁] [Scheme.Modules.Invertible L₂]
variable {s : (L₁ ⊗ L₂).sections}

/-- Flat pullback along the first projection of a tensor-section splitting is
bijective on every Chow group. -/
theorem firstProjectionPullback_bijective
    (C : Scheme.TensorSectionSplitting L₁ L₂ s) (k : ℤ) :
    Function.Bijective (firstProjectionPullback delta Y C k) := sorry

/-- Flat pullback along the first projection of a tensor-section splitting is
injective on every Chow group. -/
theorem firstProjectionPullback_injective
    (C : Scheme.TensorSectionSplitting L₁ L₂ s) (k : ℤ) :
    Function.Injective (firstProjectionPullback delta Y C k) := sorry

end AlgebraicGeometry.ChowGroup.TensorSectionSplitting
