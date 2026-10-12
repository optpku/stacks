/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived
public import ReasLib.CategoryTheory.Functor.Equivalence.Choice
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Remark_75_17_5_Uniqueness_of_dga_RLinearModel

/-!
# Comparison of differential graded models

Two compatible generator models of derived quasi-coherent modules on an algebraic
space are compared by derived tensoring with the cross-Hom differential graded
bimodules of their chosen generators.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Changing between two relative linear generator models is derived tensoring with the
cross-Hom bimodule from the second generator to the first. -/
theorem dgAlgebraModelComparison
    {R : Type u} [CommRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K L : CochainComplex (Modules X) ℤ)
    [K.IsKInjective] [L.IsKInjective]
    (hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n))
    (hLqc : ∀ n : ℤ, quasiCoherentModuleProperty X (L.homology n))
    (FK : RLinearModel.GeneratorModel f K hKqc)
    (FL : RLinearModel.GeneratorModel f L hLqc)
    (hKPerfect : ModuleDerived.IsPerfect (RLinearModel.generatorObject K hKqc).obj)
    (hLPerfect : ModuleDerived.IsPerfect (RLinearModel.generatorObject L hLqc).obj)
    (hKGenerator : IsWeakGenerator (RLinearModel.generatorObject K hKqc))
    (hLGenerator : IsWeakGenerator (RLinearModel.generatorObject L hLqc)) :
    Nonempty
      (FK.functor ⋙ (FL.functor.asEquivalenceOf FL.isEquivalence).inverse ≅
        DifferentialGradedBimodule.Tensor.derivedFunctor
          (RLinearModel.bimodule f L K)) := sorry

/-- The inverse change between two relative linear generator models is derived tensoring with
the cross-Hom bimodule from the first generator to the second. -/
theorem dgAlgebraModelComparison_symm
    {R : Type u} [CommRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    (K L : CochainComplex (Modules X) ℤ)
    [K.IsKInjective] [L.IsKInjective]
    (hKqc : ∀ n : ℤ, quasiCoherentModuleProperty X (K.homology n))
    (hLqc : ∀ n : ℤ, quasiCoherentModuleProperty X (L.homology n))
    (FK : RLinearModel.GeneratorModel f K hKqc)
    (FL : RLinearModel.GeneratorModel f L hLqc)
    (hKPerfect : ModuleDerived.IsPerfect (RLinearModel.generatorObject K hKqc).obj)
    (hLPerfect : ModuleDerived.IsPerfect (RLinearModel.generatorObject L hLqc).obj)
    (hKGenerator : IsWeakGenerator (RLinearModel.generatorObject K hKqc))
    (hLGenerator : IsWeakGenerator (RLinearModel.generatorObject L hLqc)) :
    Nonempty
      (FL.functor ⋙ (FK.functor.asEquivalenceOf FK.isEquivalence).inverse ≅
        DifferentialGradedBimodule.Tensor.derivedFunctor
          (RLinearModel.bimodule f K L)) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
