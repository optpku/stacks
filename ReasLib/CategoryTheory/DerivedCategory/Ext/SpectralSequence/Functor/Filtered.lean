module

public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Functor.Basic
public import ReasLib.CategoryTheory.Filtration.Complex.Quotient.Comparison

/-!
# Filtered functorial extension groups

This leaf specializes the basic derived-Ext actions to filtered complexes.  It provides target
stage/graded functors and comparison maps, together with source quotient/graded functors and the
quotient-to-underlying natural transformation.  The underlying filtered-complex and quotient
functors are the neutral owners from `CategoryTheory.FilteredComplex`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated ShiftedHom
open scoped DerivedExt

noncomputable section

universe t w v u

namespace CategoryTheory.DerivedCategory.Ext

section Derived

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{t} A]

namespace Target

/-- The target-Ext functor on filtered complexes, obtained from the underlying complex. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
noncomputable def filteredFunctor (M : DerivedCategory A) (n : ℤ) :
    FilteredComplex A ⥤ AddCommGrpCat.{t} :=
  FilteredComplex.underlyingFunctor ⋙ DerivedCategory.Q ⋙ functor M n

@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem filteredFunctor_obj (M : DerivedCategory A) (n : ℤ) (K : FilteredComplex A) :
    (filteredFunctor M n).obj K = addCommGrp M (DerivedCategory.Q.obj K.underlying) n := rfl

@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem filteredFunctor_map {M : DerivedCategory A} {K L : FilteredComplex A}
    (n : ℤ) (f : K ⟶ L) :
    (filteredFunctor M n).map f = ShiftedHom.postcomp M
      (DerivedCategory.Q.map (FilteredComplex.underlyingMap f)) n := rfl

/-- The target-Ext functor on a fixed filtration stage. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z]
noncomputable def stageFunctor (M : DerivedCategory A) (p n : ℤ) :
    FilteredComplex A ⥤ AddCommGrpCat.{t} :=
  FilteredComplex.Stage.functor p ⋙ DerivedCategory.Q ⋙ functor M n

@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z]
theorem stageFunctor_obj (M : DerivedCategory A) (p n : ℤ) (K : FilteredComplex A) :
    (stageFunctor M p n).obj K =
      addCommGrp M (DerivedCategory.Q.obj (K.stage p)) n := rfl

@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z]
theorem stageFunctor_map {M : DerivedCategory A} {K L : FilteredComplex A}
    (p n : ℤ) (f : K ⟶ L) :
    (stageFunctor M p n).map f = ShiftedHom.postcomp M
      (DerivedCategory.Q.map (FilteredComplex.stageMap f p)) n := rfl

/-! The graded-piece and stage-comparison target functors. -/

/-- The target-Ext functor on the `p`-th graded-piece complex. -/
@[stacks 0G1Y]
noncomputable def gradedFunctor (M : DerivedCategory A) (p n : ℤ) :
    FilteredComplex A ⥤ AddCommGrpCat.{t} :=
  FilteredComplex.gradedPieceFunctor p ⋙ DerivedCategory.Q ⋙ functor M n

@[simp, stacks 0G1Y]
theorem gradedFunctor_obj (M : DerivedCategory A) (p n : ℤ) (K : FilteredComplex A) :
    (gradedFunctor M p n).obj K =
      addCommGrp M (DerivedCategory.Q.obj (K.gradedPiece p)) n := rfl

@[simp, stacks 0G1Y]
theorem gradedFunctor_map {M : DerivedCategory A} {K L : FilteredComplex A}
    (p n : ℤ) (f : K ⟶ L) :
    (gradedFunctor M p n).map f = ShiftedHom.postcomp M
      (DerivedCategory.Q.map (FilteredComplex.gradedPieceMap f p)) n := rfl

/-- The Ext map induced by a comparison `F^q K ⟶ F^p K`. -/
@[stacks 0G1X]
noncomputable def stageComparisonMap (M : DerivedCategory A) (K : FilteredComplex A)
    {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    (stageFunctor M q n).obj K ⟶ (stageFunctor M p n).obj K :=
  ShiftedHom.postcomp M (DerivedCategory.Q.map (K.stageComparison hpq)) n

@[simp, stacks 0G1X]
theorem stageComparisonMap_eq (M : DerivedCategory A) (K : FilteredComplex A)
    {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    stageComparisonMap M K hpq n =
      ShiftedHom.postcomp M (DerivedCategory.Q.map (K.stageComparison hpq)) n := rfl

@[simp, stacks 0G1X]
theorem stageComparisonMap_eq_functorMap (M : DerivedCategory A) (K : FilteredComplex A)
    {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    stageComparisonMap M K hpq n =
      (functor M n).map (DerivedCategory.Q.map (K.stageComparison hpq)) := rfl

@[simp, stacks 0G1X]
theorem stageComparisonMap_refl (M : DerivedCategory A) (K : FilteredComplex A)
    (p n : ℤ) :
    stageComparisonMap M K (le_refl p) n = 𝟙 ((stageFunctor M p n).obj K) := sorry

@[simp, reassoc, stacks 0G1X]
theorem stageComparisonMap_comp (M : DerivedCategory A) (K : FilteredComplex A)
    {p q r : ℤ} (hpq : p ≤ q) (hqr : q ≤ r) (n : ℤ) :
    stageComparisonMap M K hqr n ≫ stageComparisonMap M K hpq n =
      stageComparisonMap M K (hpq.trans hqr) n := sorry

/-- The stage comparison maps are natural in the filtered complex. -/
@[reassoc, stacks 0G1X]
theorem stageComparisonMap_naturality {M : DerivedCategory A}
    {K L : FilteredComplex A} {p q : ℤ} (hpq : p ≤ q) (n : ℤ) (f : K ⟶ L) :
    stageComparisonMap M K hpq n ≫ (stageFunctor M p n).map f =
      (stageFunctor M q n).map f ≫ stageComparisonMap M L hpq n := sorry

/-! The two canonical maps used by the eventual target-filtration hypotheses. -/

/-- The Ext map induced by the inclusion of a filtration stage into the underlying complex. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z]
noncomputable def stageInclusionMap (M : DerivedCategory A) (K : FilteredComplex A)
    (p n : ℤ) :
    (stageFunctor M p n).obj K ⟶ (filteredFunctor M n).obj K :=
  ShiftedHom.postcomp M (DerivedCategory.Q.map (K.stageInclusion p)) n

@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z]
theorem stageInclusionMap_eq (M : DerivedCategory A) (K : FilteredComplex A)
    (p n : ℤ) :
    stageInclusionMap M K p n =
      ShiftedHom.postcomp M (DerivedCategory.Q.map (K.stageInclusion p)) n := rfl

/-- The stage-inclusion map is the morphism action of the target Ext functor. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z]
theorem stageInclusionMap_eq_functorMap (M : DerivedCategory A)
    (K : FilteredComplex A) (p n : ℤ) :
    stageInclusionMap M K p n =
      (functor M n).map (DerivedCategory.Q.map (K.stageInclusion p)) := rfl

/-- The stage-inclusion Ext maps form a natural square for filtered-complex morphisms. -/
@[reassoc, stacks 0G1X, stacks 0G1Y, stacks 0G1Z]
theorem stageInclusionMap_naturality {M : DerivedCategory A}
    {K L : FilteredComplex A} (p n : ℤ) (f : K ⟶ L) :
    stageInclusionMap M K p n ≫ (filteredFunctor M n).map f =
      (stageFunctor M p n).map f ≫ stageInclusionMap M L p n := sorry

/-- A stage comparison followed by the inclusion into the underlying complex is the later-stage
inclusion. -/
@[reassoc, stacks 0G1X]
theorem stageComparisonMap_comp_inclusion {M : DerivedCategory A}
    (K : FilteredComplex A) {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    stageComparisonMap M K hpq n ≫ stageInclusionMap M K p n =
      stageInclusionMap M K q n := sorry

end Target

namespace Source

/-- The source-Ext functor on the `p`-th graded-piece complex. -/
@[stacks 0G1Z]
noncomputable def gradedFunctor (K : DerivedCategory A) (p n : ℤ) :
    (FilteredComplex A)ᵒᵖ ⥤ AddCommGrpCat.{t} :=
  (FilteredComplex.gradedPieceFunctor p).op ⋙ DerivedCategory.Q.op ⋙
    ShiftedHom.AddCommGrp.sourceFunctor K n

@[simp, stacks 0G1Z]
theorem gradedFunctor_obj (K : DerivedCategory A) (p n : ℤ)
    (M : (FilteredComplex A)ᵒᵖ) :
    (gradedFunctor K p n).obj M =
      addCommGrp (DerivedCategory.Q.obj (M.unop.gradedPiece p)) K n := rfl

@[simp, stacks 0G1Z]
theorem gradedFunctor_map {K : DerivedCategory A}
    {M N : (FilteredComplex A)ᵒᵖ} (p n : ℤ) (f : M ⟶ N) :
    (gradedFunctor K p n).map f =
      ShiftedHom.precomp
        (DerivedCategory.Q.map (FilteredComplex.gradedPieceMap f.unop p)) K n := rfl

/-- The source-Ext functor on filtered complexes, evaluated through the underlying complex.

The opposite category keeps the source variance covariant.  This is a composition of the
canonical underlying-complex functor, localization, and the neutral shifted-Hom source owner.
-/
@[stacks 0G1Z]
noncomputable def filteredFunctor (K : DerivedCategory A) (n : ℤ) :
    (FilteredComplex A)ᵒᵖ ⥤ AddCommGrpCat.{t} :=
  FilteredComplex.underlyingFunctor.op ⋙ DerivedCategory.Q.op ⋙
    ShiftedHom.AddCommGrp.sourceFunctor K n

@[simp, stacks 0G1Z]
theorem filteredFunctor_obj (K : DerivedCategory A) (n : ℤ)
    (M : (FilteredComplex A)ᵒᵖ) :
    (filteredFunctor K n).obj M =
      addCommGrp (DerivedCategory.Q.obj M.unop.underlying) K n := rfl

@[simp, stacks 0G1Z]
theorem filteredFunctor_map {K : DerivedCategory A}
    {M N : (FilteredComplex A)ᵒᵖ} (n : ℤ) (f : M ⟶ N) :
    (filteredFunctor K n).map f =
      ShiftedHom.precomp
        (DerivedCategory.Q.map (FilteredComplex.underlyingMap f.unop)) K n := rfl

/-- The source-Ext functor on the `p`-th quotient of a filtered complex. -/
@[stacks 0G1Z]
noncomputable def quotientFunctor (K : DerivedCategory A) (p n : ℤ) :
    (FilteredComplex A)ᵒᵖ ⥤ AddCommGrpCat.{t} :=
  (FilteredComplex.quotientFunctor p).op ⋙ DerivedCategory.Q.op ⋙
    ShiftedHom.AddCommGrp.sourceFunctor K n

@[simp, stacks 0G1Z]
theorem quotientFunctor_obj (K : DerivedCategory A) (p n : ℤ)
    (M : (FilteredComplex A)ᵒᵖ) :
    (quotientFunctor K p n).obj M =
      addCommGrp (DerivedCategory.Q.obj (M.unop.quotient p)) K n := rfl

@[simp, stacks 0G1Z]
theorem quotientFunctor_map {K : DerivedCategory A}
    {M N : (FilteredComplex A)ᵒᵖ} (p n : ℤ) (f : M ⟶ N) :
    (quotientFunctor K p n).map f =
      ShiftedHom.precomp
        (DerivedCategory.Q.map (FilteredComplex.quotientMap f.unop p)) K n := rfl

/-- The Ext map from a filtered source quotient to its underlying complex. -/
@[stacks 0G1Z]
noncomputable def quotientMap (M : FilteredComplex A) (K : DerivedCategory A) (p n : ℤ) :
    addCommGrp (DerivedCategory.Q.obj (M.quotient p)) K n ⟶
      addCommGrp (DerivedCategory.Q.obj M.underlying) K n :=
  ShiftedHom.precomp (DerivedCategory.Q.map (M.underlyingToQuotient p)) K n

@[simp, stacks 0G1Z]
theorem quotientMap_eq (M : FilteredComplex A) (K : DerivedCategory A) (p n : ℤ) :
    quotientMap M K p n =
      ShiftedHom.precomp (DerivedCategory.Q.map (M.underlyingToQuotient p)) K n := rfl

/-- The source-quotient map is the morphism action of the source Ext functor. -/
@[stacks 0G1Z]
theorem quotientMap_eq_functorMap (M : FilteredComplex A)
    (K : DerivedCategory A) (p n : ℤ) :
    quotientMap M K p n =
      (functor K n).map (DerivedCategory.Q.map (M.underlyingToQuotient p)).op := rfl

/-- The source-quotient maps are natural in the filtered source. -/
@[reassoc, stacks 0G1Z]
theorem quotientMap_naturality {M N : FilteredComplex A} (f : M ⟶ N)
    (K : DerivedCategory A) (p n : ℤ) :
    quotientMap N K p n ≫
        ShiftedHom.precomp (DerivedCategory.Q.map (FilteredComplex.underlyingMap f)) K n =
        ShiftedHom.precomp (DerivedCategory.Q.map (FilteredComplex.quotientMap f p)) K n ≫
        quotientMap M K p n := sorry

/-- The quotient-to-underlying maps form a natural transformation of source-Ext functors.

The data owner is the neutral filtered-complex projection `Quotient.fromUnderlying`; taking its
opposite and whiskering with the localized source-Ext functor supplies the variance-correct
transformation without rebuilding the naturality square here. -/
@[stacks 0G1Z]
noncomputable abbrev quotientNatTrans (K : DerivedCategory A) (p n : ℤ) :
    quotientFunctor K p n ⟶ filteredFunctor K n :=
  Functor.whiskerRight (NatTrans.op (FilteredComplex.Quotient.fromUnderlying p))
    (DerivedCategory.Q.op ⋙ ShiftedHom.AddCommGrp.sourceFunctor K n)

end Source

end Derived

end CategoryTheory.DerivedCategory.Ext
