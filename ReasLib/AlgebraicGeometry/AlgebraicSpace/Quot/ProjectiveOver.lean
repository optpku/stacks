/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace.MorphismProperties
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.RationalHilbert
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Proper

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- The Hilbert Quot functor of a quasi-coherent sheaf on projective space over an
algebraic space, with rational Hilbert polynomial `P` relative to `𝒪(1)`. -/
def quotHilbertProjectiveOver (n : ℕ) {S : Scheme.{u}} (B : AlgebraicSpace S)
    (F : (ProjectiveSpace n B).Modules) [F.IsQuasicoherent] (P : Polynomial ℚ) :
    Subfunctor (quot (ProjectiveSpace.toBase n B) F) :=
  quotRationalHilbert (ProjectiveSpace.toBase n B) F (ProjectiveSpace.twistingSheaf n B) P

/-- The Hilbert Quot functor of a finitely presented sheaf on projective space over an
algebraic space is represented by an algebraic space proper over the base. -/
theorem quotHilbertProjectiveOver_isProperOver {S : Scheme.{u}} (B : AlgebraicSpace S)
    (n : ℕ) (F : (ProjectiveSpace n B).Modules) [F.IsFinitePresentation]
    (P : Polynomial ℚ) :
    IsProperOver (quotHilbertProjectiveOver n B F P).toFunctor := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
