/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Functor
public import ReasLib.CategoryTheory.Filtration.Complex.Functors

/-!
# Computation rules for filtered complexes

The constructions in `Filtration.Complex.Functors` are induced by functors on filtered objects.
This leaf exposes their term, differential, morphism, and short-complex computations so
applications do not have to unfold `mapHomologicalComplex`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

namespace FilteredComplex

open FilteredObject

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]

/-- The underlying complex has the underlying object of the filtered complex in each degree. -/
@[simp, stacks 012C]
theorem underlying_X (K : FilteredComplex 𝒜) (n : ℤ) :
    K.underlying.X n = (K.X n).obj := sorry

/-- The differentials of the underlying complex are the underlying filtered differentials. -/
@[simp, stacks 012C]
theorem underlying_d (K : FilteredComplex 𝒜) (i j : ℤ) :
    K.underlying.d i j = (K.d i j).hom := sorry

/-- A map of underlying complexes is evaluated by forgetting the corresponding filtered map. -/
@[simp, stacks 012C]
theorem underlyingMap_f {K L : FilteredComplex 𝒜} (f : K ⟶ L) (n : ℤ) :
    (K.underlyingMap f).f n = (f.f n).hom := sorry

/-- The short complex of the underlying complex is obtained by forgetting the filtered short
complex in the same degree. -/
@[simp, stacks 012C]
theorem underlying_sc (K : FilteredComplex 𝒜) (n : ℤ) :
    K.underlying.sc n = (K.sc n).map FilteredObject.forget := sorry

/-- The stage complex has the selected filtration stage in each degree. -/
@[simp, stacks 012C]
theorem stage_X (K : FilteredComplex 𝒜) (p n : ℤ) :
    (K.stage p).X n = (K.X n).filtration.stage p := sorry

/-- The stage-complex differential is induced by the corresponding filtered differential. -/
@[simp, stacks 012C]
theorem stage_d (K : FilteredComplex 𝒜) (p i j : ℤ) :
    (K.stage p).d i j = (K.d i j).stageMap p := sorry

/-- A map of stage complexes is evaluated by the stage map of the filtered component. -/
@[simp, stacks 012C]
theorem stageMap_f {K L : FilteredComplex 𝒜} (f : K ⟶ L) (p n : ℤ) :
    (K.stageMap f p).f n = (f.f n).stageMap p := sorry

/-- The degree component of a stage inclusion is the corresponding stage-to-underlying map. -/
@[simp, stacks 012C]
theorem stageInclusion_f (K : FilteredComplex 𝒜) (p n : ℤ) :
    (K.stageInclusion p).f n = (FilteredObject.Stage.toForget p).app (K.X n) := sorry

/-- The degree component of a stage comparison is the filtration inclusion in that degree. -/
@[simp, stacks 012C]
theorem stageComparison_f (K : FilteredComplex 𝒜) {p q : ℤ}
    (hpq : p ≤ q) (n : ℤ) :
    (K.stageComparison hpq).f n = (K.X n).filtration.inclusion hpq := sorry

/-- The short complex of a stage complex is the stagewise image of the filtered short complex. -/
@[simp, stacks 012C]
theorem stage_sc (K : FilteredComplex 𝒜) (p n : ℤ) :
    (K.stage p).sc n = (K.sc n).map (FilteredObject.Stage.functor p) := sorry

section Graded

variable [HasCokernels 𝒜]

/-- The associated graded complex has the associated graded filtered object in each degree. -/
@[simp, stacks 012C]
theorem associatedGraded_X (K : FilteredComplex 𝒜) (n : ℤ) :
    K.associatedGraded.X n = (K.X n).associatedGraded := sorry

/-- The associated graded differential is induced by the corresponding filtered differential. -/
@[simp, stacks 012C]
theorem associatedGraded_d (K : FilteredComplex 𝒜) (i j : ℤ) :
    K.associatedGraded.d i j = (K.d i j).associatedGradedMap := sorry

/-- A map of associated graded complexes is evaluated by the associated graded map of its
filtered component. -/
@[simp, stacks 012C]
theorem associatedGradedMap_f {K L : FilteredComplex 𝒜} (f : K ⟶ L) (n : ℤ) :
    (K.associatedGradedMap f).f n = (f.f n).associatedGradedMap := sorry

/-- The short complex of an associated graded complex is the associated graded image of the
filtered short complex. -/
@[simp, stacks 012C]
theorem associatedGraded_sc (K : FilteredComplex 𝒜) (n : ℤ) :
    K.associatedGraded.sc n =
      (K.sc n).map FilteredObject.associatedGradedFunctor := sorry

/-- The graded-piece complex has the selected associated graded piece in each degree. -/
@[simp, stacks 012C]
theorem gradedPiece_X (K : FilteredComplex 𝒜) (p n : ℤ) :
    (K.gradedPiece p).X n = (K.X n).associatedGraded p := sorry

/-- The graded-piece differential is induced by the corresponding filtered differential. -/
@[simp, stacks 012C]
theorem gradedPiece_d (K : FilteredComplex 𝒜) (p i j : ℤ) :
    (K.gradedPiece p).d i j = (K.d i j).gradedPieceMap p := sorry

/-- A map of graded-piece complexes is evaluated by the graded-piece map of its filtered
component. -/
@[simp, stacks 012C]
theorem gradedPieceMap_f {K L : FilteredComplex 𝒜} (f : K ⟶ L) (p n : ℤ) :
    (K.gradedPieceMap f p).f n = (f.f n).gradedPieceMap p := sorry

/-- The short complex of a graded-piece complex is the corresponding graded-piece image of the
filtered short complex. -/
@[simp, stacks 012C]
theorem gradedPiece_sc (K : FilteredComplex 𝒜) (p n : ℤ) :
    (K.gradedPiece p).sc n =
      (K.sc n).map (FilteredObject.associatedGradedFunctor ⋙ GradedObject.eval p) := sorry

end Graded

end FilteredComplex

end CategoryTheory
