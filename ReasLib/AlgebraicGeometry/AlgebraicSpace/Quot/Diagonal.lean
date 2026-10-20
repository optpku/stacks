/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver.MorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport

/-!
# The diagonal of the Grothendieck Quot functor

The relative diagonal of the Grothendieck Quot functor over `B` is a closed
immersion, and of finite presentation when the source module is of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The diagonal of `quot f F` over `B` is a closed immersion. -/
theorem isClosedImmersion_diagonal (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent] :
    SchemeOver.IsClosedImmersion (Limits.diag (quot f F)) := sorry

/-- If `F` is of finite type, then the diagonal of `quot f F`
over `B` is of finite presentation. -/
theorem finitePresentation_diagonal (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    SchemeOver.IsFinitePresentation (Limits.diag (quot f F)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
