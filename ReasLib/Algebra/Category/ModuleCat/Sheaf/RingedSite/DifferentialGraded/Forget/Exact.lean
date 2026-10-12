/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.GradedModule.EvaluationCokernels
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
noncomputable section
universe u v w

namespace SheafOfModules.RingedSite
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}} (A : DGA(O))

namespace DifferentialGradedAlgebra.GradedModule

attribute [-instance] instAbelian in
theorem evaluation_preservesFiniteLimits (i : ℤ) : PreservesFiniteLimits (evaluation A i) := by
  letI : ∀ {M N : GradedModule A} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (evaluation A i) := fun f ↦ evaluation_preservesKernel f i
  letI : HasZeroObject (GradedModule A) := hasZeroObject_of_hasTerminal_object
  letI : HasBinaryBiproducts (GradedModule A) := HasBinaryBiproducts.of_hasBinaryProducts
  exact Functor.preservesFiniteLimits_of_preservesKernels (evaluation A i)

attribute [-instance] instAbelian in
theorem evaluation_preservesFiniteColimits (i : ℤ) : PreservesFiniteColimits (evaluation A i) := by
  letI : ∀ {M N : GradedModule A} (f : M ⟶ N),
      PreservesColimit (parallelPair f 0) (evaluation A i) := fun f ↦ evaluation_preservesCokernel f i
  letI : HasZeroObject (GradedModule A) := hasZeroObject_of_hasTerminal_object
  letI : HasBinaryBiproducts (GradedModule A) := HasBinaryBiproducts.of_hasBinaryProducts
  exact Functor.preservesFiniteColimits_of_preservesCokernels (evaluation A i)

end DifferentialGradedAlgebra.GradedModule

namespace DifferentialGradedModule

/-- Forgetting to complexes then evaluating is the same actual functor as forgetting to graded modules then evaluating. -/
theorem forget_evaluation (i : ℤ) :
    forgetToComplex A ⋙ HomologicalComplex.eval (ringedSiteModuleCategory.{u,v,w,w} J O)
        (ComplexShape.up ℤ) i =
      forgetToGraded A ⋙ DifferentialGradedAlgebra.GradedModule.evaluation A i := rfl

/-- DG-module short exactness implies short exactness of its actual underlying cochain complex. -/
theorem shortExact_forgetToComplex (S : ShortComplex Mod(A, d)) (hS : S.ShortExact) :
    (S.map (forgetToComplex A)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  letI := DifferentialGradedAlgebra.GradedModule.evaluation_preservesFiniteLimits A i
  letI := DifferentialGradedAlgebra.GradedModule.evaluation_preservesFiniteColimits A i
  have hdegree := hS.map_of_exact
    (forgetToGraded A ⋙ DifferentialGradedAlgebra.GradedModule.evaluation A i)
  rw [← ShortComplex.map_comp]
  exact hdegree

/-- The long cohomology sequence uses the canonical connecting map of the actual underlying sequence. -/
theorem homologySequence_exact (S : ShortComplex Mod(A, d)) (hS : S.ShortExact) (i : ℤ) :
    (HomologicalComplex.HomologySequence.composableArrows₅
      (shortExact_forgetToComplex A S hS) i (i+1) (ComplexShape.up_mk i (i+1) rfl)).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact
    (shortExact_forgetToComplex A S hS) i (i+1) (ComplexShape.up_mk i (i+1) rfl)

end DifferentialGradedModule
end SheafOfModules.RingedSite
