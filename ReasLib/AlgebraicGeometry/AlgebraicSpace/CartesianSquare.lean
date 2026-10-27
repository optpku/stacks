/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- In a commutative two-square diagram of algebraic spaces over a scheme, if the left
square and the outer rectangle are cartesian and the lower-left horizontal morphism is
surjective étale, then the right square is cartesian. -/
theorem isPullback_of_left_of_surjective_etale
    {S : Scheme.{u}} {A B C D E F : AlgebraicSpace S}
    {fAC : A ⟶ C} {fAB : A ⟶ B} {fCD : C ⟶ D} {fBD : B ⟶ D}
    {fCE : C ⟶ E} {fEF : E ⟶ F} {fDF : D ⟶ F}
    (hABCD : IsPullback fAC fAB fCD fBD)
    (hABEF : IsPullback (fAC ≫ fCE) fAB fEF (fBD ≫ fDF))
    (wCDEF : fCE ≫ fEF = fCD ≫ fDF) [Surjective fBD] [Etale fBD] :
    IsPullback fCE fCD fEF fDF :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
