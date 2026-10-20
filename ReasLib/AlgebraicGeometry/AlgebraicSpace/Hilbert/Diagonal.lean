/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver.MorphismProperty

/-!
# The diagonal of the Grothendieck Hilbert functor

The relative diagonal of the Hilbert functor over `B` is a closed immersion
of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The diagonal of `hilbert f` over `B` is a closed immersion when `f` is
separated and of finite presentation. -/
theorem isClosedImmersion_diagonal (f : X ⟶ B) [FinitePresentation f]
    [Separated f] :
    SchemeOver.IsClosedImmersion (Limits.diag (hilbert f)) := sorry

/-- The diagonal of `hilbert f` over `B` is of finite presentation when `f` is
separated and of finite presentation. -/
theorem finitePresentation_diagonal (f : X ⟶ B) [FinitePresentation f]
    [Separated f] :
    SchemeOver.IsFinitePresentation (Limits.diag (hilbert f)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
