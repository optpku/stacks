/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFiniteType

/-!
# Fixed relative dimension and fpqc locality

Having a fixed relative dimension is local on the target for the fpqc
precoverage of schemes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom.RelativeDimension

/-- Having a fixed relative dimension is local on the target for the fpqc
precoverage. -/
instance isLocalAtTargetFpqc (d : ℕ) :
    MorphismProperty.IsLocalAtTarget
      ((fun _ _ f ↦ AlgebraicGeometry.Scheme.Hom.RelativeDimension f d) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.Scheme.Hom.RelativeDimension
