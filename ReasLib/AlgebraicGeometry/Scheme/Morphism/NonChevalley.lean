/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.Topology.LocallyClosed.FiniteUnion

/-!
# A finite-presentation morphism with a non-finite-locally-closed image
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- There are affine schemes and a finite-presentation morphism between them with a locally closed
subset whose image is not a finite union of locally closed subsets. -/
theorem exists_affine_finitePresentation_locallyClosed_image_not_finiteUnion :
    ∃ (X Y : Scheme.{u}) (_ : IsAffine X) (_ : IsAffine Y) (f : X ⟶ Y)
      (_ : Scheme.Hom.FinitePresentation f) (T : Set X),
      IsLocallyClosed T ∧ ¬ IsFiniteUnionOfLocallyClosed (f.base '' T) := sorry

end AlgebraicGeometry
