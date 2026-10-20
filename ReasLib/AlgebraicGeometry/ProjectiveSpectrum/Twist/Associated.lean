module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Functorial
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Tensor
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical tensor-twist morphisms for associated sheaves

This file constructs the canonical morphism from the tensor twist of an associated sheaf to the
associated sheaf of the shifted graded module. Its construction is independent of the formula
on standard opens; that geometric refinement belongs to the downstream shift-comparison API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison

open GradedModule.TensorProduct

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]
variable [DirectSum.Decomposition ℳ]

/-- The tensor right-unit map preserves total degree when its regular-grading input is shifted
by `k` and its output grading is shifted by the same amount. -/
@[stacks 01MQ "degree preservation for the tensor right-unit shift map"]
theorem tensorRid_mapsTo (k i : ℤ) :
    Set.MapsTo (TensorProduct.rid A M).toLinearMap
      (grading A ℳ
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading 𝒜) k) i)
      (GradedModule.shiftGrading ℳ k i) := sorry

/-- Stacks `01MQ`: the canonical morphism from the tensor twist of an associated module sheaf
to the associated sheaf of the shifted module grading. -/
@[stacks 01MQ "canonical associated-module tensor-twist morphism"]
noncomputable def canonicalHom (k : ℤ) :
    (tensorObj (sheaf 𝒜 ℳ) (twistingSheaf (R := ℤ) (A := A) 𝒜 k) :
      (Proj 𝒜).Modules) ⟶ sheaf 𝒜 (GradedModule.shiftGrading ℳ k) :=
  Tensor.hom 𝒜 ℳ
      (GradedModule.shiftGrading
        (DirectSum.Decomposition.natToIntGrading 𝒜) k) ≫
    map 𝒜
      (gradingFor A 𝒜 ℳ
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading 𝒜) k))
      (GradedModule.shiftGrading ℳ k)
      (TensorProduct.rid A M).toLinearMap
      (tensorRid_mapsTo 𝒜 ℳ k)

end AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison

end
