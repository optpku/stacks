/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.Shift.NatInt
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.GradedSections
public import ReasLib.RingTheory.GradedAlgebra.GeneratedBy
import Mathlib.Tactic.CrossRefAttribute

/-!
# Eventual sections of associated module sheaves

This module constructs the canonical maps from the homogeneous pieces of an internally graded
module to the global sections of the corresponding tensor twists of its associated sheaf.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Proj.AssociatedModule.ShiftedSections

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]

/-- The degree-`n` piece is the degree-zero piece of the grading shifted by `n`. -/
@[stacks 0B5R "degree as the zero piece of a shifted grading"]
theorem degree_eq_shift_zero (ℳ : ℤ → Submodule ℤ M) (n : ℤ) :
    ℳ n = GradedModule.shiftGrading ℳ n 0 := sorry

/-- The sheaves associated to all translated module gradings, equipped with the canonical maps
from the corresponding homogeneous pieces to global sections. -/
@[stacks 0B5R "presentation of shifted associated sheaves"]
noncomputable def presentation :
    Proj.AssociatedModule.Presentation 𝒜 (fun n : ℤ ↦ (ℳ n : Type u)) :=
  Proj.AssociatedModule.Presentation.ofFamily
    (fun n : ℤ ↦ sheaf 𝒜 (GradedModule.shiftGrading ℳ n))
    (fun n : ℤ ↦
      (degreeZeroToGlobalSections 𝒜 (GradedModule.shiftGrading ℳ n)).toAddMonoidHom.comp
        (AddEquiv.toAddMonoidHom <|
          AddEquiv.cast (M := fun N : Submodule ℤ M ↦ (N : Type u)) (degree_eq_shift_zero ℳ n)))

/-- The canonical map from a homogeneous piece to the global sections of the corresponding
tensor twist, transported along a comparison with the associated sheaf of the translated
grading. -/
@[stacks 0AG7 "map from a homogeneous piece to tensor-twist sections"]
noncomputable def toTensorTwist
    (comparisonIso : ∀ n : ℤ,
      ProjTwistFamily.tensorTwist (twistingSheaf 𝒜) (sheaf 𝒜 ℳ) n ≅
        sheaf 𝒜 (GradedModule.shiftGrading ℳ n))
    (n : ℤ) :
    AddCommGrpCat.of (ℳ n) ⟶
      AddCommGrpCat.of
        (Γ(ProjTwistFamily.tensorTwist (twistingSheaf 𝒜) (sheaf 𝒜 ℳ) n, ⊤)) :=
  AddCommGrpCat.ofHom <|
    Proj.AssociatedModule.Presentation.sectionMapOfIso
      (presentation 𝒜 ℳ) (comparisonIso n)

/-- For a finite graded module over a finite-type degree-one-generated graded ring with
Noetherian degree-zero part, the canonical maps to twisted global sections are isomorphisms in
all sufficiently large degrees. -/
@[stacks 0AG7 "eventual isomorphism to tensor-twist sections"]
theorem toTensorTwist_eventually_isIso
    [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)]
    (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1)
    [DirectSum.Decomposition ℳ] [Module.Finite A M]
    (comparisonIso : ∀ n : ℤ,
      ProjTwistFamily.tensorTwist (twistingSheaf 𝒜) (sheaf 𝒜 ℳ) n ≅
        sheaf 𝒜 (GradedModule.shiftGrading ℳ n)) :
    ∃ b : ℤ, ∀ n : ℤ, b ≤ n →
      IsIso (toTensorTwist 𝒜 ℳ comparisonIso n) := sorry

end AlgebraicGeometry.Proj.AssociatedModule.ShiftedSections
