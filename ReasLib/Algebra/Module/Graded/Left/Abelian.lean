module

public import ReasLib.Algebra.Module.Graded.Left.Category
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Abelian left graded modules

The category of left graded modules over a graded ring is abelian.
-/

@[expose] public section

noncomputable section

universe x w v u

open CategoryTheory Limits

namespace GradedModule.Left

variable {ι : Type x} [DecidableEq ι] [AddMonoid ι]
variable {κ : Type x} [DecidableEq κ] [AddAction ι κ]
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]

/-- 052N: Left graded modules over a graded ring form an abelian category. -/
@[stacks 052N]
noncomputable instance instAbelian : Abelian (Left.{x, w, v, u} 𝒜 κ) where
  toPreadditive := inferInstance
  normalMonoOfMono := sorry
  normalEpiOfEpi := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

end GradedModule.Left
