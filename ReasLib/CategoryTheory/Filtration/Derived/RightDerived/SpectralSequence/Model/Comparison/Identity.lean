/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Model.Comparison.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity compatibility for filtered right-derived comparisons

Identity resolution maps preserve all selected model comparisons.
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

namespace Model.Comparison

namespace IsCompatible

/-- Identity maps commute with every chosen stage comparison. -/
@[stacks 0BKK "identity naturality of filtered right-derived model comparisons"]
theorem idStage {K : FilteredComplex A} {R : KInjectiveResolution K}
    (P : Comparison F R) :
    ∀ p n : ℤ,
      CommSq (HomologicalComplex.homologyMap
          (FilteredComplex.stageMap (modelMap F (KInjectiveResolution.Map.id R)) p) n)
        (P.stageIso p n).hom (P.stageIso p n).hom
        (cochainCohomologyMap F (FilteredComplex.stageMap (𝟙 K) p) n) := sorry

/-- Identity maps commute with every chosen graded-piece comparison. -/
@[stacks 0BKK "identity naturality of filtered right-derived model comparisons"]
theorem idGradedPiece {K : FilteredComplex A} {R : KInjectiveResolution K}
    (P : Comparison F R) :
    ∀ p n : ℤ,
      CommSq (HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap
            (modelMap F (KInjectiveResolution.Map.id R)) p) n)
        (P.gradedPieceIso p n).hom (P.gradedPieceIso p n).hom
        (cochainCohomologyMap F (FilteredComplex.gradedPieceMap (𝟙 K) p) n) := sorry

/-- Identity maps commute with every chosen underlying-complex comparison. -/
@[stacks 0BKK "identity naturality of filtered right-derived model comparisons"]
theorem idUnderlying {K : FilteredComplex A} {R : KInjectiveResolution K}
    (P : Comparison F R) :
    ∀ n : ℤ,
      CommSq (HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap (modelMap F (KInjectiveResolution.Map.id R))) n)
        (P.underlyingIso n).hom (P.underlyingIso n).hom
        (cochainCohomologyMap F (FilteredComplex.underlyingMap (𝟙 K)) n) := sorry

/-- Identity naturality for a chosen filtered right-derived model comparison. -/
@[stacks 0BKK "identity morphism of filtered right-derived model comparisons"]
theorem id {K : FilteredComplex A} {R : KInjectiveResolution K}
    (P : Comparison F R) :
    IsCompatible F (KInjectiveResolution.Map.id R) P P := sorry

end IsCompatible

end Model.Comparison

end CategoryTheory.FilteredComplex.RightDerived
