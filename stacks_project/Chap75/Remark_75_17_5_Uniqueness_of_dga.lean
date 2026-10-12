/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Remark_75_17_5_Uniqueness_of_dga_Comparison
public import stacks_project.Chap75.Remark_75_17_5_Uniqueness_of_dga_RLinearModel
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Remark 75.17.5 (Uniqueness of dga) (1): for a qcqs algebraic space `X` over a ring
`R`, changing between the compatible `R`-linear DG models arising from K-injective
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
      (FK : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.GeneratorModel
        f K hKqc)
      (FL : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.GeneratorModel
        f L hLqc)
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
      Nonempty
        (FK.functor ⋙ (FL.functor.asEquivalenceOf FL.isEquivalence).inverse ≅
          DifferentialGradedBimodule.Tensor.derivedFunctor
            (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.bimodule
              f L K)))

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
      (FK : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.GeneratorModel
        f K hKqc)
      (FL : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.GeneratorModel
        f L hLqc)
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
      Nonempty
        (FL.functor ⋙ (FK.functor.asEquivalenceOf FK.isEquivalence).inverse ≅
          DifferentialGradedBimodule.Tensor.derivedFunctor
            (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.RLinearModel.bimodule
              f K L)))
