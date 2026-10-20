/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Curve

variable {k : Type u} [Field k]

/-- Every curve over a field is either affine or H-projective over that field. -/
theorem isAffine_or_hProjective
    (X : Over (Spec (CommRingCat.of k))) [Curve X] :
    IsAffine X.left ∨ HProjective X.hom := sorry

end AlgebraicGeometry.Curve
