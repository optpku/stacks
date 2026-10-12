/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.FiniteType

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- There exist affine schemes `X` and `S`, a finitely presented morphism `X ⟶ S`,
and a finitely presented module on `X` that is pure over `S` but not universally pure over `S`. -/
theorem exists_isPureOver_not_isUniversallyPureOver :
    ∃ (X S : Scheme.{u}) (_ : IsAffine X) (_ : IsAffine S) (f : X ⟶ S)
      (_ : Scheme.Hom.FinitePresentation f) (ℱ : X.Modules)
      (_ : ℱ.IsFinitePresentation),
      ℱ.IsPureOver f ∧ ¬ ℱ.IsUniversallyPureOver f := sorry

end AlgebraicGeometry.Scheme.Modules
