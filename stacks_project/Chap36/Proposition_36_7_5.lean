module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison.AffineDiagonal
public import stacks_project.Chap36.Lemma_36_4_1

@[expose] public section

open CategoryTheory Limits

universe u

/- Proposition 36.7.5: for a quasi-compact scheme with affine diagonal, the canonical
comparison functor is an equivalence with the derived coherator composite as quasi-inverse. -/
@[stacks 08DB]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.comparison_isQuasiInverse_of_compact_affineDiagonal :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X]
      [AlgebraicGeometry.IsAffineHom (prod.lift (𝟙 X) (𝟙 X))],
      (AlgebraicGeometry.Scheme.DerivedQCoh.comparison X).IsQuasiInverse
        ((DerivedCategory.cohomologyIn
            (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
          (AlgebraicGeometry.Scheme.Modules.ringedSpaceEquivalence X).mapDerivedCategory.inverse ⋙
          AlgebraicGeometry.Scheme.QCoh.Derived.coherator X))

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.comparisonIsEquivalenceOfCompactAffineDiagonal :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X]
      [AlgebraicGeometry.IsAffineHom (prod.lift (𝟙 X) (𝟙 X))],
      (AlgebraicGeometry.Scheme.DerivedQCoh.comparison X).IsEquivalence)
