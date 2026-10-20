module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Locus.Flat
import StacksCheckRecall

universe u

/- Lemma 31.9.7 (1): the coproduct of the Fitting rank loci represents the functor on
`Sch/S` that is a singleton exactly when the pulled-back module is flat. -/
@[stacks 05P9] #check
  (AlgebraicGeometry.Scheme.fittingFlatLocus_nonempty_over_hom_iff_isFlat :
    ∀ {S T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ S) (F : S.Modules)
      [F.IsFinitePresentation],
      Subsingleton
          (CategoryTheory.Over.mk g ⟶
            CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.fittingFlatLocusι F)) ∧
        (Nonempty
            (CategoryTheory.Over.mk g ⟶
              CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.fittingFlatLocusι F)) ↔
          SheafOfModules.IsFlat
            ((AlgebraicGeometry.Scheme.Modules.pullback g).obj F)))

/- Lemma 31.9.7 (2): on the rank-`r` Fitting locus, the restricted module is finite locally
free of rank `r`. -/
@[stacks 05P9] #check
  (AlgebraicGeometry.Scheme.fittingRankLocus_pullback_isFiniteLocallyFreeOfRank :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (F : S.Modules) [F.IsFinitePresentation] (r : ℕ),
      SheafOfModules.IsFiniteLocallyFreeOfRank r
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.fittingRankLocusι F r)).obj F))

/- Lemma 31.9.7 (3): each rank-`r` Fitting locus maps to the ambient scheme by a morphism of
finite presentation. -/
@[stacks 05P9] #check
  (AlgebraicGeometry.Scheme.fittingRankLocus_hom_finitePresentation :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (F : S.Modules) [F.IsFinitePresentation] (r : ℕ),
      AlgebraicGeometry.Scheme.Hom.FinitePresentation
        (AlgebraicGeometry.Scheme.fittingRankLocusι F r))

/- Lemma 31.9.7 (4): the coproduct of all Fitting rank loci maps to the ambient scheme by a
morphism of finite presentation. -/
@[stacks 05P9] #check
  (AlgebraicGeometry.Scheme.fittingFlatLocus_hom_finitePresentation :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (F : S.Modules) [F.IsFinitePresentation],
      AlgebraicGeometry.Scheme.Hom.FinitePresentation
        (AlgebraicGeometry.Scheme.fittingFlatLocusι F))
