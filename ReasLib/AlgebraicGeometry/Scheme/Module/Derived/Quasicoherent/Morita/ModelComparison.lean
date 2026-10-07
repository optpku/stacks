module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RLinearModel
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Tensor
public import ReasLib.CategoryTheory.Functor.Equivalence.Choice

/-!
# Comparison of Differential Graded Models

Two compatible generator models of derived quasicoherent modules are compared by derived
tensoring with the cross-Hom differential graded bimodules of their chosen generators.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Changing between two relative linear generator models is derived tensoring with the
cross-Hom bimodule from the second generator to the first. -/
theorem dgAlgebraModelComparison
    {R : Type u} [CommRing R] {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (f : X ⟶ Spec (CommRingCat.of R))
    (K L : CochainComplex X.toRingedSpace.Modules ℤ)
    [K.IsKInjective] [L.IsKInjective]
    (hKqc : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (K.homology n))
    (hLqc : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (L.homology n))
    (FK : RLinearModel.GeneratorModel f K hKqc)
    (FL : RLinearModel.GeneratorModel f L hLqc)
    (hKPerfect : RingedSpace.ModuleDerived.IsPerfect
      (RLinearModel.generatorObject K hKqc).obj)
    (hLPerfect : RingedSpace.ModuleDerived.IsPerfect
      (RLinearModel.generatorObject L hLqc).obj)
    (hKGenerator : IsWeakGenerator (RLinearModel.generatorObject K hKqc))
    (hLGenerator : IsWeakGenerator (RLinearModel.generatorObject L hLqc)) :
    Nonempty
      (FK.functor ⋙ (FL.functor.asEquivalenceOf FL.isEquivalence).inverse ≅
        DifferentialGradedBimodule.Tensor.derivedFunctor
          (RLinearModel.bimodule f L K)) := sorry

/-- The inverse change between two relative linear generator models is derived tensoring with
the cross-Hom bimodule from the first generator to the second. -/
theorem dgAlgebraModelComparison_symm
    {R : Type u} [CommRing R] {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (f : X ⟶ Spec (CommRingCat.of R))
    (K L : CochainComplex X.toRingedSpace.Modules ℤ)
    [K.IsKInjective] [L.IsKInjective]
    (hKqc : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (K.homology n))
    (hLqc : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (L.homology n))
    (FK : RLinearModel.GeneratorModel f K hKqc)
    (FL : RLinearModel.GeneratorModel f L hLqc)
    (hKPerfect : RingedSpace.ModuleDerived.IsPerfect
      (RLinearModel.generatorObject K hKqc).obj)
    (hLPerfect : RingedSpace.ModuleDerived.IsPerfect
      (RLinearModel.generatorObject L hLqc).obj)
    (hKGenerator : IsWeakGenerator (RLinearModel.generatorObject K hKqc))
    (hLGenerator : IsWeakGenerator (RLinearModel.generatorObject L hLqc)) :
    Nonempty
      (FL.functor ⋙ (FK.functor.asEquivalenceOf FK.isEquivalence).inverse ≅
        DifferentialGradedBimodule.Tensor.derivedFunctor
          (RLinearModel.bimodule f K L)) := sorry

section Integral

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (K L : CochainComplex X.toRingedSpace.Modules ℤ)
variable [K.IsKInjective] [L.IsKInjective]

/-- For integral generator models, changing from the model defined by `K` to the model defined
by `L` is derived tensoring with the cross-Hom bimodule `Hom(L, K)`. -/
theorem dgAlgebraModelComparison_int
    (hKqc : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (K.homology n))
    (hLqc : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (L.homology n))
    (hKPerfect : RingedSpace.ModuleDerived.IsPerfect
      (RLinearModel.generatorObject K hKqc).obj)
    (hLPerfect : RingedSpace.ModuleDerived.IsPerfect
      (RLinearModel.generatorObject L hLqc).obj)
    (hKGenerator : IsWeakGenerator (RLinearModel.generatorObject K hKqc))
    (hLGenerator : IsWeakGenerator (RLinearModel.generatorObject L hLqc))
    (hFK : (tensorFunctor K hKqc).IsEquivalence)
    (hFL : (tensorFunctor L hLqc).IsEquivalence) :
    Nonempty
      (tensorFunctor K hKqc ⋙ ((tensorFunctor L hLqc).asEquivalenceOf hFL).inverse ≅
        DifferentialGradedBimodule.Tensor.derivedFunctor
          (DifferentialGradedCategory.HomComplex.bimodule L K)) := sorry

/-- For integral generator models, the inverse change from the model defined by `L` to the
model defined by `K` is derived tensoring with the cross-Hom bimodule `Hom(K, L)`. -/
theorem dgAlgebraModelComparison_symm_int
    (hKqc : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (K.homology n))
    (hLqc : ∀ n : ℤ, RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
      (L.homology n))
    (hKPerfect : RingedSpace.ModuleDerived.IsPerfect
      (RLinearModel.generatorObject K hKqc).obj)
    (hLPerfect : RingedSpace.ModuleDerived.IsPerfect
      (RLinearModel.generatorObject L hLqc).obj)
    (hKGenerator : IsWeakGenerator (RLinearModel.generatorObject K hKqc))
    (hLGenerator : IsWeakGenerator (RLinearModel.generatorObject L hLqc))
    (hFK : (tensorFunctor K hKqc).IsEquivalence)
    (hFL : (tensorFunctor L hLqc).IsEquivalence) :
    Nonempty
      (tensorFunctor L hLqc ⋙ ((tensorFunctor K hKqc).asEquivalenceOf hFK).inverse ≅
        DifferentialGradedBimodule.Tensor.derivedFunctor
          (DifferentialGradedCategory.HomComplex.bimodule K L)) := sorry

end Integral

end AlgebraicGeometry.Scheme.DerivedQCoh
