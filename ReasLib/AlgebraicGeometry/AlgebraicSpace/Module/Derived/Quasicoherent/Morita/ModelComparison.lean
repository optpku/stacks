/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RLinearModel
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Comparison of differential graded models

The canonical derived-Hom models of derived quasi-coherent modules on an algebraic
space are compared by derived tensoring with the cross-Hom differential graded
bimodules of their chosen generators.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Derived Hom from two K-injective perfect weak generators gives equivalences,
and tensoring the first with the cross-Hom bimodule from the second generator to the first
is naturally isomorphic to the second. -/
theorem dgAlgebraModelComparison
    {R : Type u} [CommRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K L : CochainComplex (Modules X) ℤ)
    [K.IsKInjective] [L.IsKInjective]
    (hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n))
    (hLqc : ∀ n : ℤ, quasiCoherentModuleProperty X (L.homology n))
    (hKPerfect : ModuleDerived.IsPerfect (RLinearModel.generatorObject K hKqc).obj)
    (hLPerfect : ModuleDerived.IsPerfect (RLinearModel.generatorObject L hLqc).obj)
    (hKGenerator : IsWeakGenerator (RLinearModel.generatorObject K hKqc))
    (hLGenerator : IsWeakGenerator (RLinearModel.generatorObject L hLqc)) :
    ((RLinearModel.functor f K).IsEquivalence ∧
      (RLinearModel.functor f L).IsEquivalence) ∧
      Nonempty (RLinearModel.functor f K ⋙
        DifferentialGradedBimodule.Tensor.derivedFunctor (RLinearModel.bimodule f L K) ≅
          RLinearModel.functor f L) := sorry

/-- Tensoring derived Hom from the second perfect weak generator with the cross-Hom
bimodule from the first generator to the second is naturally isomorphic to derived Hom
from the first. -/
theorem dgAlgebraModelComparison_symm
    {R : Type u} [CommRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K L : CochainComplex (Modules X) ℤ)
    [K.IsKInjective] [L.IsKInjective]
    (hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n))
    (hLqc : ∀ n : ℤ, quasiCoherentModuleProperty X (L.homology n))
    (hKPerfect : ModuleDerived.IsPerfect (RLinearModel.generatorObject K hKqc).obj)
    (hLPerfect : ModuleDerived.IsPerfect (RLinearModel.generatorObject L hLqc).obj)
    (hKGenerator : IsWeakGenerator (RLinearModel.generatorObject K hKqc))
    (hLGenerator : IsWeakGenerator (RLinearModel.generatorObject L hLqc)) :
    Nonempty (RLinearModel.functor f L ⋙
      DifferentialGradedBimodule.Tensor.derivedFunctor (RLinearModel.bimodule f K L) ≅
        RLinearModel.functor f K) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
