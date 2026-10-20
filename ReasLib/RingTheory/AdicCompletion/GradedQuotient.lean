module

public import ReasLib.Algebra.Category.GradedModuleCat.Category
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import Mathlib.RingTheory.AdicCompletion.Basic

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace AdicCompletion.Graded

variable {A : Type u} [CommRing A]
variable {𝒜 : ℕ → Submodule ℤ A} [GradedAlgebra 𝒜]

/-- The image grading on the quotient of a graded module by an ideal-power submodule. -/
def idealPowerQuotientGrading (I : HomogeneousIdeal 𝒜) (N : GradedModuleCat 𝒜) (n : ℕ) :
    ℤ → Submodule ℤ (N.module ⧸ I.toIdeal ^ n • (⊤ : Submodule A N.module)) :=
  fun degree ↦ (N.grading degree).map
    ((Submodule.mkQ (I.toIdeal ^ n • (⊤ : Submodule A N.module))).restrictScalars ℤ)

/-- The image grading on a homogeneous ideal-power quotient is an internal direct sum. -/
theorem idealPowerQuotient_isInternal (I : HomogeneousIdeal 𝒜)
    (N : GradedModuleCat 𝒜) (n : ℕ) :
    DirectSum.IsInternal (idealPowerQuotientGrading I N n) := sorry

/-- Homogeneous scalar multiplication descends to a homogeneous ideal-power quotient. -/
theorem idealPowerQuotient_gradedSMul (I : HomogeneousIdeal 𝒜)
    (N : GradedModuleCat 𝒜) (n : ℕ) :
    SetLike.GradedSMul 𝒜 (idealPowerQuotientGrading I N n) := sorry

/-- The graded quotient `N / I ^ n N`, with its image grading. -/
def idealPowerQuotient (I : HomogeneousIdeal 𝒜) (N : GradedModuleCat 𝒜) (n : ℕ) :
    GradedModuleCat 𝒜 :=
  GradedModuleCat.of (ModuleCat.of A (N.module ⧸ I.toIdeal ^ n • (⊤ : Submodule A N.module)))
    (idealPowerQuotientGrading I N n)
    (idealPowerQuotient_isInternal I N n) (idealPowerQuotient_gradedSMul I N n)

/-- The underlying module of a graded ideal-power quotient is the ordinary module quotient. -/
theorem idealPowerQuotient_module (I : HomogeneousIdeal 𝒜) (N : GradedModuleCat 𝒜) (n : ℕ) :
    (idealPowerQuotient I N n).module =
      ModuleCat.of A (N.module ⧸ I.toIdeal ^ n • (⊤ : Submodule A N.module)) := sorry

/-- The homogeneous pieces of the graded quotient are the images of the original pieces. -/
theorem idealPowerQuotient_grading (I : HomogeneousIdeal 𝒜) (N : GradedModuleCat 𝒜) (n : ℕ) :
    (idealPowerQuotient I N n).grading = idealPowerQuotientGrading I N n := sorry

/-- The canonical ideal-power transition map preserves the quotient homogeneous pieces. -/
theorem idealPowerQuotientTransition_mem (I : HomogeneousIdeal 𝒜)
    (N : GradedModuleCat 𝒜) (n : ℕ) (degree : ℤ)
    (element : (idealPowerQuotient I N (n + 1)).module)
    (h_mem : element ∈ (idealPowerQuotient I N (n + 1)).grading degree) :
    AdicCompletion.transitionMap I.toIdeal N.module (Nat.le_add_right n 1) element ∈
      (idealPowerQuotient I N n).grading degree := sorry

/-- The canonical graded successor map between ideal-power quotients. -/
def idealPowerQuotientStep (I : HomogeneousIdeal 𝒜) (N : GradedModuleCat 𝒜) (n : ℕ) :
    idealPowerQuotient I N (n + 1) ⟶ idealPowerQuotient I N n :=
  GradedModuleCat.Hom.ofLinearMap
    (AdicCompletion.transitionMap I.toIdeal N.module (Nat.le_add_right n 1))
    (idealPowerQuotientTransition_mem I N n)

/-- The sequential inverse system of graded quotients `n ↦ N / I ^ n N`. -/
def idealPowerQuotientSystem (I : HomogeneousIdeal 𝒜) (N : GradedModuleCat 𝒜) :
    SequentialInverseSystem (GradedModuleCat 𝒜) :=
  Functor.ofOpSequence (idealPowerQuotientStep I N)

/-- Stage `n` of the graded quotient system is `N / I ^ n N`. -/
theorem idealPowerQuotientSystem_obj (I : HomogeneousIdeal 𝒜)
    (N : GradedModuleCat 𝒜) (n : ℕ) :
    (idealPowerQuotientSystem I N).obj (op n) = idealPowerQuotient I N n := sorry

/-- Successor maps of the graded quotient system are the canonical quotient transition maps. -/
theorem idealPowerQuotientSystem_stepMap (I : HomogeneousIdeal 𝒜)
    (N : GradedModuleCat 𝒜) (n : ℕ) :
    (idealPowerQuotientSystem I N).stepMap n = idealPowerQuotientStep I N n := sorry

end AdicCompletion.Graded
