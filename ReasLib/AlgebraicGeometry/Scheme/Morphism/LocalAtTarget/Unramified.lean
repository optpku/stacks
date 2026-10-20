/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.OpenImmersion

/-!
# Target locality of unramified morphisms

Unramifiedness and G-unramifiedness of scheme morphisms are local on the target for the fpqc
precoverage.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Unramified

/-- Unramifiedness of scheme morphisms is local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Unramified : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.Unramified

namespace AlgebraicGeometry.GUnramified

/-- G-unramifiedness of scheme morphisms is local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.GUnramified : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.GUnramified
