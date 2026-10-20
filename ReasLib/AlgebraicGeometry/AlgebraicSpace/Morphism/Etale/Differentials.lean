/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Differentials

/-!
# Étale comparison for relative differentials of algebraic spaces

The canonical pullback comparison of relative differentials is invertible when
both the source and base morphisms in the square are étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Differentials

variable {S : Scheme.{u}}

/-- For a commutative square of algebraic spaces whose horizontal morphisms are étale,
the canonical pullback comparison on relative differentials is an isomorphism. -/
instance comparison_isIso_of_etale {B1 B2 X1 X2 : AlgebraicSpace S}
    {sB : B2 ⟶ B1} {f : X2 ⟶ X1} {sX1 : X1 ⟶ B1} {sX2 : X2 ⟶ B2}
    (sq : f ≫ sX1 = sX2 ≫ sB) [Etale f] [Etale sB] :
    IsIso (comparison f sB sX1 sX2 sq) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Differentials
