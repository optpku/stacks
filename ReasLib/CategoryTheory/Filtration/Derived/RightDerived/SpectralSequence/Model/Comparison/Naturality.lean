/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Model.Comparison.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality formulas for filtered right-derived comparisons

These formulas solve the selected comparison squares for the model homology maps.
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

namespace Model.Comparison.IsCompatible

/-- Naturality of a compatible model comparison on a filtration stage. -/
@[reassoc, stacks 0BKK "stage naturality of filtered right-derived model comparisons"]
theorem stage_naturality
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {m : KInjectiveResolution.Map f R S} {P : Comparison F R}
    {Q : Comparison F S} (h : IsCompatible F m P Q) (p n : ℤ) :
    HomologicalComplex.homologyMap
          (FilteredComplex.stageMap (modelMap F m) p) n ≫
        (Q.stageIso p n).hom =
      (P.stageIso p n).hom ≫
        cochainCohomologyMap F (FilteredComplex.stageMap f p) n := sorry

/-- Naturality of the inverse compatible model comparison on a filtration stage. -/
@[reassoc, stacks 0BKK "inverse stage naturality of filtered right-derived model comparisons"]
theorem stage_inv_naturality
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {m : KInjectiveResolution.Map f R S} {P : Comparison F R}
    {Q : Comparison F S} (h : IsCompatible F m P Q) (p n : ℤ) :
    cochainCohomologyMap F (FilteredComplex.stageMap f p) n ≫
        (Q.stageIso p n).inv =
      (P.stageIso p n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.stageMap (modelMap F m) p) n := sorry

/-- Naturality of a compatible model comparison on a graded piece. -/
@[reassoc, stacks 0BKK "graded-piece naturality of filtered right-derived model comparisons"]
theorem gradedPiece_naturality
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {m : KInjectiveResolution.Map f R S} {P : Comparison F R}
    {Q : Comparison F S} (h : IsCompatible F m P Q) (p n : ℤ) :
    HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap (modelMap F m) p) n ≫
        (Q.gradedPieceIso p n).hom =
      (P.gradedPieceIso p n).hom ≫
        cochainCohomologyMap F (FilteredComplex.gradedPieceMap f p) n := sorry

/-- Naturality of the inverse compatible model comparison on a graded piece. -/
@[reassoc, stacks 0BKK
  "inverse graded-piece naturality of filtered right-derived model comparisons"]
theorem gradedPiece_inv_naturality
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {m : KInjectiveResolution.Map f R S} {P : Comparison F R}
    {Q : Comparison F S} (h : IsCompatible F m P Q) (p n : ℤ) :
    cochainCohomologyMap F (FilteredComplex.gradedPieceMap f p) n ≫
        (Q.gradedPieceIso p n).inv =
      (P.gradedPieceIso p n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap (modelMap F m) p) n := sorry

/-- Naturality of a compatible model comparison on underlying complexes. -/
@[reassoc, stacks 0BKK "underlying naturality of filtered right-derived model comparisons"]
theorem underlying_naturality
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {m : KInjectiveResolution.Map f R S} {P : Comparison F R}
    {Q : Comparison F S} (h : IsCompatible F m P Q) (n : ℤ) :
    HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap (modelMap F m)) n ≫
        (Q.underlyingIso n).hom =
      (P.underlyingIso n).hom ≫
        cochainCohomologyMap F (FilteredComplex.underlyingMap f) n := sorry

/-- Naturality of the inverse compatible model comparison on underlying complexes. -/
@[reassoc, stacks 0BKK
  "inverse underlying naturality of filtered right-derived model comparisons"]
theorem underlying_inv_naturality
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {m : KInjectiveResolution.Map f R S} {P : Comparison F R}
    {Q : Comparison F S} (h : IsCompatible F m P Q) (n : ℤ) :
    cochainCohomologyMap F (FilteredComplex.underlyingMap f) n ≫
        (Q.underlyingIso n).inv =
      (P.underlyingIso n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap (modelMap F m)) n := sorry

/-- Solving the stage comparison square for the filtered-model homology map. -/
@[reassoc, stacks 0BKK "inverse stage naturality of filtered right-derived model comparisons"]
theorem stage_naturality_inv
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {m : KInjectiveResolution.Map f R S} {P : Comparison F R}
    {Q : Comparison F S} (h : IsCompatible F m P Q) (p n : ℤ) :
    (P.stageIso p n).hom ≫
        cochainCohomologyMap F (FilteredComplex.stageMap f p) n ≫
        (Q.stageIso p n).inv =
      HomologicalComplex.homologyMap
        (FilteredComplex.stageMap (modelMap F m) p) n := sorry

/-- Solving the underlying comparison square for the filtered-model homology map. -/
@[reassoc, stacks 0BKK
  "inverse underlying naturality of filtered right-derived model comparisons"]
theorem underlying_naturality_inv
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {m : KInjectiveResolution.Map f R S} {P : Comparison F R}
    {Q : Comparison F S} (h : IsCompatible F m P Q) (n : ℤ) :
    (P.underlyingIso n).hom ≫
        cochainCohomologyMap F (FilteredComplex.underlyingMap f) n ≫
        (Q.underlyingIso n).inv =
      HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap (modelMap F m)) n := sorry

/-- Solving the graded-piece comparison square for the filtered-model homology map. -/
@[reassoc, stacks 0BKK "inverse graded-piece naturality of filtered right-derived model comparisons"]
theorem gradedPiece_naturality_inv
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {m : KInjectiveResolution.Map f R S} {P : Comparison F R}
    {Q : Comparison F S} (h : IsCompatible F m P Q) (p n : ℤ) :
    (P.gradedPieceIso p n).hom ≫
        cochainCohomologyMap F (FilteredComplex.gradedPieceMap f p) n ≫
        (Q.gradedPieceIso p n).inv =
      HomologicalComplex.homologyMap
        (FilteredComplex.gradedPieceMap (modelMap F m) p) n := sorry

/-- Conjugating the filtered-model stage homology map by the inverse comparison recovers the
cohomology map of the original stage. -/
@[reassoc, stacks 0BKK "target-map computation for filtered right-derived stages"]
theorem stage_target_map
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {m : KInjectiveResolution.Map f R S} {P : Comparison F R}
    {Q : Comparison F S} (h : IsCompatible F m P Q) (p n : ℤ) :
    (P.stageIso p n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.stageMap (modelMap F m) p) n ≫
      (Q.stageIso p n).hom =
    cochainCohomologyMap F (FilteredComplex.stageMap f p) n := sorry

/-- Conjugating the filtered-model graded-piece homology map by the inverse comparison recovers
the cohomology map of the original graded piece. -/
@[reassoc, stacks 0BKK "target-map computation for filtered right-derived graded pieces"]
theorem gradedPiece_target_map
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {m : KInjectiveResolution.Map f R S} {P : Comparison F R}
    {Q : Comparison F S} (h : IsCompatible F m P Q) (p n : ℤ) :
    (P.gradedPieceIso p n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap (modelMap F m) p) n ≫
      (Q.gradedPieceIso p n).hom =
    cochainCohomologyMap F (FilteredComplex.gradedPieceMap f p) n := sorry

/-- Conjugating the filtered-model underlying homology map by the inverse comparison recovers the
cohomology map of the original underlying complex. -/
@[reassoc, stacks 0BKK "target-map computation for filtered right-derived underlying complexes"]
theorem underlying_target_map
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {m : KInjectiveResolution.Map f R S} {P : Comparison F R}
    {Q : Comparison F S} (h : IsCompatible F m P Q) (n : ℤ) :
    (P.underlyingIso n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap (modelMap F m)) n ≫
      (Q.underlyingIso n).hom =
    cochainCohomologyMap F (FilteredComplex.underlyingMap f) n := sorry

end Model.Comparison.IsCompatible

end CategoryTheory.FilteredComplex.RightDerived
