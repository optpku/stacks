module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Model
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology comparisons for filtered right-derived models

This file packages stage, graded-piece, and underlying cohomology comparisons and their compatibility with resolution maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open Functor.RightDerived.Homotopy

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace Model

/-- Chosen cohomology comparisons between a filtered K-injective model and total
right-derived cohomology of the original filtration views. -/
@[stacks 0BKK "cohomology comparison for a filtered right-derived model"]
structure Comparison {K : FilteredComplex A} (R : KInjectiveResolution K) where
  /-- Comparison on every filtration stage. -/
  stageIso : ∀ p n : ℤ,
    ((model F R).stage p).homology n ≅ cochainCohomology F (K.stage p) n
  /-- Comparison on every graded piece. -/
  gradedPieceIso : ∀ p n : ℤ,
    ((model F R).gradedPiece p).homology n ≅ cochainCohomology F (K.gradedPiece p) n
  /-- Comparison on the underlying complex. -/
  underlyingIso : ∀ n : ℤ,
    (model F R).underlying.homology n ≅ cochainCohomology F K.underlying n
  /-- Naturality of the stage comparison with respect to inclusion into the underlying complex. -/
  stageInclusionSq : ∀ p n : ℤ,
    CommSq (HomologicalComplex.homologyMap ((model F R).stageInclusion p) n)
      (stageIso p n).hom (underlyingIso n).hom
      (cochainCohomologyMap F (K.stageInclusion p) n)

/-- Every explicit filtered K-injective resolution carries chosen model comparisons. -/
@[stacks 0BKK "cohomology comparison for a filtered right-derived model"]
theorem Comparison.nonempty {K : FilteredComplex A} (R : KInjectiveResolution K) :
    Nonempty (Comparison F R) := sorry

namespace Comparison

/-- Compatibility of model comparisons along a morphism of filtered K-injective resolutions. -/
@[stacks 0BKK "naturality of filtered right-derived model comparisons"]
structure IsCompatible {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    (m : KInjectiveResolution.Map f R S) (P : Comparison F R)
    (Q : Comparison F S) : Prop where
  /-- Naturality on every filtration stage. -/
  stageSq : ∀ p n : ℤ,
    CommSq (HomologicalComplex.homologyMap (FilteredComplex.stageMap (modelMap F m) p) n)
      (P.stageIso p n).hom (Q.stageIso p n).hom
      (cochainCohomologyMap F (FilteredComplex.stageMap f p) n)
  /-- Naturality on every graded piece. -/
  gradedPieceSq : ∀ p n : ℤ,
    CommSq (HomologicalComplex.homologyMap (FilteredComplex.gradedPieceMap (modelMap F m) p) n)
      (P.gradedPieceIso p n).hom (Q.gradedPieceIso p n).hom
      (cochainCohomologyMap F (FilteredComplex.gradedPieceMap f p) n)
  /-- Naturality on the underlying complexes. -/
  underlyingSq : ∀ n : ℤ,
    CommSq (HomologicalComplex.homologyMap (FilteredComplex.underlyingMap (modelMap F m)) n)
      (P.underlyingIso n).hom (Q.underlyingIso n).hom
      (cochainCohomologyMap F (FilteredComplex.underlyingMap f) n)


end Comparison

end Model

end CategoryTheory.FilteredComplex.RightDerived

