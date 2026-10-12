/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Model.Comparison.GradedPiece
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Model.Comparison.Underlying

/-!
# Canonical resolution comparisons for finite right-derived models

The canonical graded-piece and underlying comparison isomorphisms assemble into a
`Model.Comparison`.  Their naturality supplies compatibility along every map of strict
filtered-injective resolutions.
-/

@[expose] public section

open CategoryTheory
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model.Comparison

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- The canonical model comparison supplied by a strict finite filtered-injective resolution. -/
@[stacks 015W "canonical comparison for a finite filtered right-derived model"]
noncomputable def ofResolution (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K) : Comparison T R where
  gradedPieceIso := GradedPiece.homologyIso T R
  underlyingIso := Underlying.homologyIso T R

/-- The graded-piece field of the canonical resolution comparison is the canonical composite
through cochains, the bounded derived category, and the pointwise derived value. -/
@[simp, stacks 015W "canonical comparison for a finite filtered right-derived model"]
theorem ofResolution_gradedPieceIso (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K) (p n : ℤ) :
    (ofResolution T R).gradedPieceIso p n = GradedPiece.homologyIso T R p n := sorry

/-- The underlying field of the canonical resolution comparison is the canonical composite
through the bounded derived category and the pointwise derived value. -/
@[simp, stacks 015W "canonical comparison for a finite filtered right-derived model"]
theorem ofResolution_underlyingIso (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K) (n : ℤ) :
    (ofResolution T R).underlyingIso n = Underlying.homologyIso T R n := sorry

namespace IsCompatible

/-- Canonical resolution comparisons are compatible along every map of strict
filtered-injective resolutions. -/
@[stacks 015W "naturality of canonical finite filtered model comparisons"]
theorem ofResolution (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) :
    IsCompatible T m (Comparison.ofResolution T R) (Comparison.ofResolution T S) := sorry

end IsCompatible

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model.Comparison
