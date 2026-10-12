/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.GradedSections.Cohomology
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.ShiftedSections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-zero cohomology of shifted associated sheaves

This module specializes the generic cohomology API for a graded family of associated sheaves
obtained by shifting an internally graded module. The generic instances remain the unique
owners of the transported graded and truncated module structures.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Proj.AssociatedModule.ShiftedSections.Cohomology

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]
variable [DirectSum.Decomposition ℳ]

/-- The degree-`n` cohomology group of the sheaf associated to the grading shifted by `n`. -/
@[stacks 0B5R "degree-zero cohomology of a shifted associated sheaf"]
abbrev degree (n : ℤ) : Type u :=
  GradedSections.Cohomology.degree 𝒜
    (fun i : ℤ ↦ sheaf 𝒜 (GradedModule.shiftGrading ℳ i)) n

/-- Degree-zero cohomology of a shifted associated sheaf is canonically equivalent to its
global sections. -/
@[stacks 0B5R "degree-zero cohomology as shifted associated-sheaf sections"]
noncomputable abbrev sectionsEquiv (n : ℤ) :
    degree 𝒜 ℳ n ≃+ ShiftedSections.degree 𝒜 ℳ n :=
  GradedSections.Cohomology.sectionsEquiv 𝒜
    (fun i : ℤ ↦ sheaf 𝒜 (GradedModule.shiftGrading ℳ i)) n

/-- Homogeneous multiplication on shifted degree-zero cohomology is transported from the
canonical action on shifted associated-sheaf sections. -/
@[stacks 0B5R "homogeneous action on shifted associated-sheaf cohomology"]
theorem degree_smul {m : ℕ} {n : ℤ} (p : 𝒜 m) (x : degree 𝒜 ℳ n) :
    GradedMonoid.GSMul.smul
        (A := fun d : ℕ ↦ 𝒜 d) (M := degree 𝒜 ℳ) p x =
      (sectionsEquiv 𝒜 ℳ ((m : ℤ) + n)).symm
        (ShiftedSections.smul 𝒜 ℳ p (sectionsEquiv 𝒜 ℳ n x)) := sorry

/-- The direct sum of shifted associated-sheaf cohomology groups in degrees bounded below
by `k`. -/
@[stacks 0B5R "lower-truncated shifted associated-sheaf cohomology"]
abbrev truncated (k : ℤ) : Type u :=
  GradedSections.Cohomology.truncated 𝒜
    (fun i : ℤ ↦ sheaf 𝒜 (GradedModule.shiftGrading ℳ i)) k

/-- Lower-truncated shifted-associated-sheaf cohomology carries the ambient `A`-module
structure induced by its canonical graded action. This specialized instance exposes the result
under the short `ShiftedSections.Cohomology.truncated` owner, so downstream typeclass search does
not need to reconstruct the underlying sheaf-family expression. -/
@[stacks 0B5R "module on lower-truncated shifted associated-sheaf cohomology"]
noncomputable instance instModule (k : ℤ) : Module A (truncated 𝒜 ℳ k) :=
  GradedSections.Cohomology.instModule 𝒜
    (fun i : ℤ ↦ sheaf 𝒜 (GradedModule.shiftGrading ℳ i)) k

/-- An ambient homogeneous scalar acts on a pure truncated shifted-cohomology summand through
the degree action. -/
@[stacks 0B5R "homogeneous action on a pure shifted-cohomology summand"]
theorem smul_of (k : ℤ) {m : ℕ} (p : 𝒜 m)
    (d : {d : ℤ // k ≤ d}) (x : degree 𝒜 ℳ d.1) :
    ((p : A) •
        DirectSum.of (DirectSum.Gmodule.LowerBound.pieces k (degree 𝒜 ℳ)) d x :
      truncated 𝒜 ℳ k) =
      DirectSum.of (DirectSum.Gmodule.LowerBound.pieces k (degree 𝒜 ℳ)) (m +ᵥ d)
        (GradedMonoid.GSMul.smul
          (A := fun e : ℕ ↦ 𝒜 e) (M := degree 𝒜 ℳ) p x) := sorry

end AlgebraicGeometry.Proj.AssociatedModule.ShiftedSections.Cohomology
