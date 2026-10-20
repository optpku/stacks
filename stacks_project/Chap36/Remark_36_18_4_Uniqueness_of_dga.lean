/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Morita.ModelComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Remark 36.18.4 (Uniqueness of dga) (1): for a qcqs scheme `X` over `Spec R`,
changing between the compatible `R`-linear DG models arising from K-injective perfect weak
generators `K` and `L` is derived tensoring with the relative cross-Hom bimodule `Hom(L, K)`. -/
@[stacks 09SU] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.dgAlgebraModelComparison :
    ∀ {R : Type u} [CommRing R] {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X]
      [QuasiSeparatedSpace X] (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
      (K L : CochainComplex X.toRingedSpace.Modules ℤ)
      [K.IsKInjective] [L.IsKInjective]
      (hKqc : ∀ n : ℤ,
        AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
          (K.homology n))
      (hLqc : ∀ n : ℤ,
        AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
          (L.homology n))
      (FK : AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel.GeneratorModel f K hKqc)
      (FL : AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel.GeneratorModel f L hLqc)
      (hKPerfect : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
        (AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel.generatorObject K hKqc).obj)
      (hLPerfect : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
        (AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel.generatorObject L hLqc).obj)
      (hKGenerator : IsWeakGenerator
        (AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel.generatorObject K hKqc))
      (hLGenerator : IsWeakGenerator
        (AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel.generatorObject L hLqc)),
      Nonempty
        (FK.functor ⋙ (FL.functor.asEquivalenceOf FL.isEquivalence).inverse ≅
          DifferentialGradedBimodule.Tensor.derivedFunctor
            (AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel.bimodule f L K)))

/- Remark 36.18.4 (Uniqueness of dga) (2): the quasi-inverse change from the `L`-model
to the `K`-model is derived tensoring with the relative cross-Hom bimodule `Hom(K, L)`. -/
@[stacks 09SU] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.dgAlgebraModelComparison_symm :
    ∀ {R : Type u} [CommRing R] {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X]
      [QuasiSeparatedSpace X] (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
      (K L : CochainComplex X.toRingedSpace.Modules ℤ)
      [K.IsKInjective] [L.IsKInjective]
      (hKqc : ∀ n : ℤ,
        AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
          (K.homology n))
      (hLqc : ∀ n : ℤ,
        AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
          (L.homology n))
      (FK : AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel.GeneratorModel f K hKqc)
      (FL : AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel.GeneratorModel f L hLqc)
      (hKPerfect : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
        (AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel.generatorObject K hKqc).obj)
      (hLPerfect : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
        (AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel.generatorObject L hLqc).obj)
      (hKGenerator : IsWeakGenerator
        (AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel.generatorObject K hKqc))
      (hLGenerator : IsWeakGenerator
        (AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel.generatorObject L hLqc)),
      Nonempty
        (FL.functor ⋙ (FK.functor.asEquivalenceOf FK.isEquivalence).inverse ≅
          DifferentialGradedBimodule.Tensor.derivedFunctor
            (AlgebraicGeometry.Scheme.DerivedQCoh.RLinearModel.bimodule f K L)))
