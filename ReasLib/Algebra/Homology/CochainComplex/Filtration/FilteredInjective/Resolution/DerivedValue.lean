/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.ComputesAt
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.QuasiIso
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Value.Replacement

/-!
# Pointwise Derived Values Computed by Filtered-Injective Resolutions

The graded-piece and underlying comparisons of a strict filtered-injective resolution are
bounded-below quasi-isomorphisms with termwise-injective targets.  They therefore compute the
pointwise right-derived values of the corresponding source complexes.  The explicit interfaces
in this module require no local computation or pointwise-definedness instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

noncomputable section

universe v v' u u'

namespace CochainComplex.FilteredInjectivePlus.Resolution

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D]

namespace GradedPiece

/-- The homotopy comparison on a graded piece belongs to the canonical bounded-below
quasi-isomorphism class. -/
@[stacks 05TW "graded-piece resolution denominator"]
theorem comparison_mem
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) (p : ℤ) :
    HomotopyCategory.Plus.quasiIso C (R.gradedPieceHomotopyComparison p) := sorry

/-- A strict filtered-injective resolution supplies pointwise right-derived definedness at each
source graded piece. -/
@[stacks 05TH "pointwise derived definedness from a graded-piece resolution"]
theorem hasPointwise (F : HomotopyCategory.Plus C ⥤ D)
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) (p : ℤ) :
    F.HasPointwiseRightDerivedFunctorAt (HomotopyCategory.Plus.quasiIso C)
      ((FilteredObject.Finite.Plus.GradedPiece.homotopy C p).obj K) := sorry

/-- The value of a functor on the graded-piece resolution target, identified with the pointwise
right-derived value of the source graded piece. -/
@[stacks 05TH "pointwise derived value computed by a graded-piece resolution"]
noncomputable def valueIso (F : HomotopyCategory.Plus C ⥤ D)
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) (p : ℤ) :=
  @RightDerived.Value.replacementIso _ _ _ _ F
    (HomotopyCategory.Plus.quasiIso C) _ _ _
    (R.gradedPieceHomotopyComparison p) (comparison_mem R p)
    (hasPointwise F R p)
    (FilteredInjectivePlus.GradedPiece.computesAt F p R.complex)

/-- The forward graded-piece resolution comparison is the canonical pointwise-derived
denominator leg. -/
@[simp, stacks 05TH "graded-piece resolution value comparison, hom"]
theorem valueIso_hom (F : HomotopyCategory.Plus C ⥤ D)
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) (p : ℤ) :
    (valueIso F R p).hom =
      @RightDerived.Value.ι _ _ _ _ F (HomotopyCategory.Plus.quasiIso C) _ _
        (R.gradedPieceHomotopyComparison p) (comparison_mem R p)
        (hasPointwise F R p) := sorry

/-- The inverse graded-piece resolution comparison is the inverse canonical denominator leg. -/
@[simp, stacks 05TH "graded-piece resolution value comparison, inv"]
theorem valueIso_inv (F : HomotopyCategory.Plus C ⥤ D)
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) (p : ℤ) :
    (valueIso F R p).inv =
      @CategoryTheory.inv _ _ _ _
        (@RightDerived.Value.ι _ _ _ _ F (HomotopyCategory.Plus.quasiIso C) _ _
          (R.gradedPieceHomotopyComparison p) (comparison_mem R p)
          (hasPointwise F R p))
        (@RightDerived.Value.isIso_ι_of_computesAt _ _ _ _ F
          (HomotopyCategory.Plus.quasiIso C) _ _ _
          (R.gradedPieceHomotopyComparison p) (comparison_mem R p)
          (hasPointwise F R p)
          (FilteredInjectivePlus.GradedPiece.computesAt F p R.complex)) := sorry

end GradedPiece

namespace Underlying

/-- The underlying homotopy comparison belongs to the canonical bounded-below
quasi-isomorphism class. -/
@[stacks 05TW "underlying resolution denominator"]
theorem comparison_mem
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) :
    HomotopyCategory.Plus.quasiIso C R.underlyingHomotopyComparison := sorry

/-- A strict filtered-injective resolution supplies pointwise right-derived definedness at the
underlying source complex. -/
@[stacks 05TH "pointwise derived definedness from an underlying resolution"]
theorem hasPointwise (F : HomotopyCategory.Plus C ⥤ D)
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) :
    F.HasPointwiseRightDerivedFunctorAt (HomotopyCategory.Plus.quasiIso C)
      ((FilteredObject.Finite.Plus.Forget.homotopy C).obj K) := sorry

/-- The value of a functor on the underlying resolution target, identified with the pointwise
right-derived value of the underlying source complex. -/
@[stacks 05TH "pointwise derived value computed by an underlying resolution"]
noncomputable def valueIso (F : HomotopyCategory.Plus C ⥤ D)
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) :=
  @RightDerived.Value.replacementIso _ _ _ _ F
    (HomotopyCategory.Plus.quasiIso C) _ _ _
    R.underlyingHomotopyComparison (comparison_mem R)
    (hasPointwise F R)
    (FilteredInjectivePlus.Underlying.computesAt F R.complex)

/-- The forward underlying resolution comparison is the canonical pointwise-derived
denominator leg. -/
@[simp, stacks 05TH "underlying resolution value comparison, hom"]
theorem valueIso_hom (F : HomotopyCategory.Plus C ⥤ D)
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) :
    (valueIso F R).hom =
      @RightDerived.Value.ι _ _ _ _ F (HomotopyCategory.Plus.quasiIso C) _ _
        R.underlyingHomotopyComparison (comparison_mem R) (hasPointwise F R) := sorry

/-- The inverse underlying resolution comparison is the inverse canonical denominator leg. -/
@[simp, stacks 05TH "underlying resolution value comparison, inv"]
theorem valueIso_inv (F : HomotopyCategory.Plus C ⥤ D)
    {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) :
    (valueIso F R).inv =
      @CategoryTheory.inv _ _ _ _
        (@RightDerived.Value.ι _ _ _ _ F (HomotopyCategory.Plus.quasiIso C) _ _
          R.underlyingHomotopyComparison (comparison_mem R) (hasPointwise F R))
        (@RightDerived.Value.isIso_ι_of_computesAt _ _ _ _ F
          (HomotopyCategory.Plus.quasiIso C) _ _ _
          R.underlyingHomotopyComparison (comparison_mem R) (hasPointwise F R)
          (FilteredInjectivePlus.Underlying.computesAt F R.complex)) := sorry

end Underlying

namespace Map.GradedPiece

/-- Forward graded-piece resolution value comparisons are natural in maps of strict
filtered-injective resolutions. -/
@[reassoc, stacks 05TU "naturality of graded-piece resolution value comparisons"]
theorem valueIso_hom_naturality (F : HomotopyCategory.Plus C ⥤ D)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (p : ℤ) :
    F.map (m.gradedPieceHomotopyMap p) ≫
        (Resolution.GradedPiece.valueIso F S p).hom =
      (Resolution.GradedPiece.valueIso F R p).hom ≫
        @RightDerived.Value.map _ _ _ _ F (HomotopyCategory.Plus.quasiIso C) _ _
          ((FilteredObject.Finite.Plus.GradedPiece.homotopy C p).map f)
          (Resolution.GradedPiece.hasPointwise F R p)
          (Resolution.GradedPiece.hasPointwise F S p) := sorry

/-- Inverse graded-piece resolution value comparisons satisfy reverse naturality in maps of
strict filtered-injective resolutions. -/
@[reassoc, stacks 05TU "inverse naturality of graded-piece resolution value comparisons"]
theorem valueIso_inv_naturality (F : HomotopyCategory.Plus C ⥤ D)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (p : ℤ) :
    (Resolution.GradedPiece.valueIso F R p).inv ≫
        F.map (m.gradedPieceHomotopyMap p) =
      @RightDerived.Value.map _ _ _ _ F (HomotopyCategory.Plus.quasiIso C) _ _
          ((FilteredObject.Finite.Plus.GradedPiece.homotopy C p).map f)
          (Resolution.GradedPiece.hasPointwise F R p)
          (Resolution.GradedPiece.hasPointwise F S p) ≫
        (Resolution.GradedPiece.valueIso F S p).inv := sorry

end Map.GradedPiece

namespace Map.Underlying

/-- Forward underlying resolution value comparisons are natural in maps of strict
filtered-injective resolutions. -/
@[reassoc, stacks 05TU "naturality of underlying resolution value comparisons"]
theorem valueIso_hom_naturality (F : HomotopyCategory.Plus C ⥤ D)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) :
    F.map m.underlyingHomotopyMap ≫ (Resolution.Underlying.valueIso F S).hom =
      (Resolution.Underlying.valueIso F R).hom ≫
        @RightDerived.Value.map _ _ _ _ F (HomotopyCategory.Plus.quasiIso C) _ _
          ((FilteredObject.Finite.Plus.Forget.homotopy C).map f)
          (Resolution.Underlying.hasPointwise F R)
          (Resolution.Underlying.hasPointwise F S) := sorry

/-- Inverse underlying resolution value comparisons satisfy reverse naturality in maps of
strict filtered-injective resolutions. -/
@[reassoc, stacks 05TU "inverse naturality of underlying resolution value comparisons"]
theorem valueIso_inv_naturality (F : HomotopyCategory.Plus C ⥤ D)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) :
    (Resolution.Underlying.valueIso F R).inv ≫ F.map m.underlyingHomotopyMap =
      @RightDerived.Value.map _ _ _ _ F (HomotopyCategory.Plus.quasiIso C) _ _
          ((FilteredObject.Finite.Plus.Forget.homotopy C).map f)
          (Resolution.Underlying.hasPointwise F R)
          (Resolution.Underlying.hasPointwise F S) ≫
        (Resolution.Underlying.valueIso F S).inv := sorry

end Map.Underlying

end CochainComplex.FilteredInjectivePlus.Resolution
