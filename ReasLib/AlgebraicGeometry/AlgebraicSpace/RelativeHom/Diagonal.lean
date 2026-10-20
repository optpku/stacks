/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.MorphismFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver.MorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# The diagonal of the relative-Hom functor

The relative diagonal of `Mor_B(Y, X)` is a closed immersion of finite
presentation when `Y ⟶ B` is flat, proper, and of finite presentation and
`X ⟶ B` is separated and of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

/-- The diagonal of `mor y x` over `B` is a closed immersion when `y` is flat,
proper, and of finite presentation and `x` is separated and of finite presentation. -/
theorem isClosedImmersion_diagonal (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x] :
    SchemeOver.IsClosedImmersion (Limits.diag (mor y x)) := sorry

/-- The diagonal of `mor y x` over `B` is of finite presentation when `y` is
flat, proper, and of finite presentation and `x` is separated and of finite presentation. -/
theorem finitePresentation_diagonal (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x] :
    SchemeOver.IsFinitePresentation (Limits.diag (mor y x)) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
