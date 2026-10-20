module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Morita.ModelComparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Remark 75.17.5 (Uniqueness of dga) (1): for a qcqs algebraic space `X` over a ring
`R`, changing between the canonical `R`-linear DG models arising from K-injective
perfect weak generators `K` and `L` is derived tensoring with the relative cross-Hom
bimodule `Hom(L, K)`, which is the setup of Remark 22.37.10. -/
@[stacks 0DK9] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.dgAlgebraModelComparison :
    ∀ {R : Type u} [CommRing R]
      {X : AlgebraicSpace (Spec (CommRingCat.of R))}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
      (K L : CochainComplex (Modules X) ℤ)
      [K.IsKInjective] [L.IsKInjective]
      (hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n))
      (hLqc : ∀ n : ℤ, quasiCoherentModuleProperty X (L.homology n))
      (hKPerfect : ModuleDerived.IsPerfect
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.generatorObject
          K hKqc).obj)
      (hLPerfect : ModuleDerived.IsPerfect
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.generatorObject
          L hLqc).obj)
      (hKGenerator : IsWeakGenerator
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.generatorObject
          K hKqc))
      (hLGenerator : IsWeakGenerator
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.generatorObject
          L hLqc)),
      ((AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.functor f K).IsEquivalence ∧
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.functor f L).IsEquivalence) ∧
        Nonempty (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.functor f K ⋙
          DifferentialGradedBimodule.Tensor.derivedFunctor
            (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.bimodule f L K) ≅
              AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.functor f L))

/- Remark 75.17.5 (Uniqueness of dga) (2): the quasi-inverse change from the `L`-model
to the `K`-model is derived tensoring with the relative cross-Hom bimodule `Hom(K, L)`. -/
@[stacks 0DK9] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.dgAlgebraModelComparison_symm :
    ∀ {R : Type u} [CommRing R]
      {X : AlgebraicSpace (Spec (CommRingCat.of R))}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
      (K L : CochainComplex (Modules X) ℤ)
      [K.IsKInjective] [L.IsKInjective]
      (hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n))
      (hLqc : ∀ n : ℤ, quasiCoherentModuleProperty X (L.homology n))
      (hKPerfect : ModuleDerived.IsPerfect
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.generatorObject
          K hKqc).obj)
      (hLPerfect : ModuleDerived.IsPerfect
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.generatorObject
          L hLqc).obj)
      (hKGenerator : IsWeakGenerator
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.generatorObject
          K hKqc))
      (hLGenerator : IsWeakGenerator
        (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.generatorObject
          L hLqc)),
      Nonempty (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.functor f L ⋙
        DifferentialGradedBimodule.Tensor.derivedFunctor
          (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.bimodule f K L) ≅
            AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.functor f K))
