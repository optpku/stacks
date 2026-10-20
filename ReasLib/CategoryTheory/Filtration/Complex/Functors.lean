/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Functors
public import ReasLib.CategoryTheory.Filtration.Complex.Definition
public import Mathlib.Algebra.Homology.Additive

/-!
# Functors on Filtered Cochain Complexes

This module is the cochain-complex facade for the category-independent functors in
`Filtration/Functors`. It owns only the `FilteredComplex` bridge; arbitrary homological complexes
reuse the neutral owner directly.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

/-! ## Filtered complex bridge layer -/

section FilteredComplexBridge

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]

namespace FilteredComplex

open FilteredObject

/-- The functor forgetting the filtration on filtered cochain complexes. -/
@[stacks 012C "underlying functor of a filtered cochain complex"]
abbrev underlyingFunctor : FilteredComplex 𝒜 ⥤ CochainComplex 𝒜 ℤ :=
  HomologicalComplex.Filtered.underlyingFunctor

/-- Forget the filtration on a filtered cochain complex. -/
abbrev underlying (K : FilteredComplex 𝒜) : CochainComplex 𝒜 ℤ :=
  underlyingFunctor.obj K

/-- The morphism on underlying cochain complexes induced by a morphism of filtered complexes. -/
abbrev underlyingMap {K L : FilteredComplex 𝒜} (α : K ⟶ L) :
    K.underlying ⟶ L.underlying :=
  underlyingFunctor.map α

/-- The underlying map induced by an identity filtered cochain-complex morphism is the identity.
-/
@[simp, stacks 012C "identity map on underlying filtered cochain complexes"]
theorem underlyingMap_id (K : FilteredComplex 𝒜) :
    K.underlyingMap (𝟙 K) = 𝟙 K.underlying := sorry

/-- Underlying maps of filtered cochain complexes preserve composition. -/
@[simp, stacks 012C "composition of underlying filtered cochain-complex maps"]
theorem underlyingMap_comp {K L M : FilteredComplex 𝒜}
    (f : K ⟶ L) (g : L ⟶ M) :
    K.underlyingMap (f ≫ g) = K.underlyingMap f ≫ L.underlyingMap g := sorry

namespace Stage

/-- Evaluation at filtration stage `p` as a functor on filtered cochain complexes. -/
@[stacks 012C "filtration-stage functor on filtered cochain complexes"]
abbrev functor (p : ℤ) : FilteredComplex 𝒜 ⥤ CochainComplex 𝒜 ℤ :=
  HomologicalComplex.Filtered.Stage.functor p

end Stage

/-- Evaluate a filtered cochain complex at the `p`-th filtration stage. -/
abbrev stage (K : FilteredComplex 𝒜) (p : ℤ) : CochainComplex 𝒜 ℤ :=
  (Stage.functor p).obj K

/-- The morphism on `p`-th stage complexes induced by a morphism of filtered complexes. -/
abbrev stageMap {K L : FilteredComplex 𝒜} (α : K ⟶ L) (p : ℤ) :
    K.stage p ⟶ L.stage p :=
  (Stage.functor p).map α

/-- The map on a fixed filtration stage induced by an identity is the identity. -/
@[simp, stacks 012C "identity map on a filtered cochain-complex stage"]
theorem stageMap_id (K : FilteredComplex 𝒜) (p : ℤ) :
    K.stageMap (𝟙 K) p = 𝟙 (K.stage p) := sorry

/-- Maps on a fixed filtration stage preserve composition. -/
@[simp, stacks 012C "composition of filtered cochain-complex stage maps"]
theorem stageMap_comp {K L M : FilteredComplex 𝒜}
    (f : K ⟶ L) (g : L ⟶ M) (p : ℤ) :
    K.stageMap (f ≫ g) p = K.stageMap f p ≫ L.stageMap g p := sorry

/-- The canonical inclusion of the `p`-th filtration stage complex into the underlying complex. -/
abbrev stageInclusion (K : FilteredComplex 𝒜) (p : ℤ) :
    K.stage p ⟶ K.underlying :=
  HomologicalComplex.Filtered.Stage.inclusion K p

/-- The canonical map from the `q`-th filtration stage complex to the `p`-th stage complex
for `p ≤ q`. -/
@[stacks 012L "filtered cochain-complex stage comparison"]
abbrev stageComparison (K : FilteredComplex 𝒜) {p q : ℤ}
    (hpq : p ≤ q) : K.stage q ⟶ K.stage p :=
  HomologicalComplex.Filtered.Stage.comparison K hpq

/-- The comparison from a filtration stage to itself is the identity. -/
@[simp, stacks 012L "identity filtered cochain-complex stage comparison"]
theorem stageComparison_refl (K : FilteredComplex 𝒜) (p : ℤ) :
    K.stageComparison (le_refl p) = 𝟙 (K.stage p) := sorry

/-- Composing two filtration-stage comparisons gives the direct comparison. -/
@[stacks 012L "composition of filtered cochain-complex stage comparisons"]
theorem stageComparison_comp (K : FilteredComplex 𝒜) {p q r : ℤ}
    (hpq : p ≤ q) (hqr : q ≤ r) :
    K.stageComparison hqr ≫ K.stageComparison hpq = K.stageComparison (hpq.trans hqr) := sorry

/-- A stage comparison followed by the inclusion into the underlying complex is the inclusion
from the later stage. -/
@[stacks 012L "stage comparison followed by filtered cochain-complex inclusion"]
theorem stageComparison_comp_stageInclusion (K : FilteredComplex 𝒜) {p q : ℤ}
    (hpq : p ≤ q) :
    K.stageComparison hpq ≫ K.stageInclusion p = K.stageInclusion q := sorry

/-- A filtered cochain-complex map commutes with each filtration-stage comparison. -/
@[reassoc, stacks 012C "naturality of filtered cochain-complex stage comparison"]
theorem stageComparison_naturality {K L : FilteredComplex 𝒜} (f : K ⟶ L) {p q : ℤ}
    (hpq : p ≤ q) :
    K.stageComparison hpq ≫ K.stageMap f p =
      K.stageMap f q ≫ L.stageComparison hpq := sorry

/-- A filtered cochain-complex map commutes with each stage inclusion into the underlying
cochain complex. -/
@[reassoc, stacks 012C "naturality of filtered cochain-complex stage inclusion"]
theorem stageMap_comp_stageInclusion {K L : FilteredComplex 𝒜} (f : K ⟶ L) (p : ℤ) :
    K.stageMap f p ≫ L.stageInclusion p = K.stageInclusion p ≫ K.underlyingMap f := sorry

section Graded

variable [HasCokernels 𝒜]

/-- Apply the associated-graded functor degreewise to filtered cochain complexes. -/
@[stacks 012C "associated-graded functor on filtered cochain complexes"]
noncomputable abbrev associatedGradedFunctor :
    FilteredComplex 𝒜 ⥤ CochainComplex (GradedObject ℤ 𝒜) ℤ :=
  HomologicalComplex.Filtered.associatedGradedFunctor

/-- The associated graded complex `K.associatedGraded` of a filtered complex. -/
noncomputable abbrev associatedGraded (K : FilteredComplex 𝒜) :
    CochainComplex (GradedObject ℤ 𝒜) ℤ :=
  associatedGradedFunctor.obj K

/-- The morphism on associated graded complexes induced by a morphism of filtered complexes. -/
noncomputable abbrev associatedGradedMap {K L : FilteredComplex 𝒜} (α : K ⟶ L) :
    K.associatedGraded ⟶ L.associatedGraded :=
  associatedGradedFunctor.map α

/-- Evaluation of the associated graded complex in degree `p`, functorial in the filtered
cochain complex. -/
@[stacks 012C "graded-piece functor on filtered cochain complexes"]
noncomputable abbrev gradedPieceFunctor (p : ℤ) :
    FilteredComplex 𝒜 ⥤ CochainComplex 𝒜 ℤ :=
  HomologicalComplex.Filtered.gradedPieceFunctor p

/-- The `p`-th graded-piece complex `K.gradedPiece p` of a filtered complex. -/
noncomputable abbrev gradedPiece (K : FilteredComplex 𝒜) (p : ℤ) :
    CochainComplex 𝒜 ℤ :=
  (gradedPieceFunctor p).obj K

/-- The morphism induced on the `p`-th graded-piece complexes by a morphism of filtered
complexes. -/
noncomputable abbrev gradedPieceMap {K L : FilteredComplex 𝒜} (α : K ⟶ L) (p : ℤ) :
    FilteredComplex.gradedPiece K p ⟶ FilteredComplex.gradedPiece L p :=
  (gradedPieceFunctor p).map α

end Graded

end FilteredComplex

end FilteredComplexBridge

end CategoryTheory
