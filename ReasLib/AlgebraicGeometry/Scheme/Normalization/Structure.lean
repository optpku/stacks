/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Normalization

@[expose] public section

/-!
# The normalization structure morphism

This leaf owns the module-theoretic structure morphism of a scheme
normalization and its cokernel.  Stalkwise and curve-specific consequences
belong in separate leaves.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Normalization.Structure

variable (X : Scheme.{u})
variable [QuasiCompact (genericPointSpectrumCoproductTo X)]
variable [QuasiSeparated (genericPointSpectrumCoproductTo X)]

/-- The direct image of the unit module on the normalization of `X`. -/
noncomputable abbrev pushforwardUnit : X.Modules :=
  (Scheme.Modules.pushforward X.normalizationTo).obj
    (SheafOfModules.unit X.normalization.ringCatSheaf : X.normalization.Modules)

/-- The canonical `𝒪_X`-linear structure morphism `𝒪_X ⟶ ν_*𝒪_{X^ν}`. -/
noncomputable abbrev map :
    SheafOfModules.unit X.ringCatSheaf ⟶ pushforwardUnit X :=
  SheafOfModules.unitToPushforwardObjUnit
    (RingedSpace.Hom.toRingCatSheafHom X.normalizationTo.toShHom)

/-- The cokernel `ν_*𝒪_{X^ν} / 𝒪_X` of the normalization structure morphism. -/
noncomputable abbrev quotient : X.Modules :=
  Limits.cokernel (map X)

end AlgebraicGeometry.Scheme.Normalization.Structure
