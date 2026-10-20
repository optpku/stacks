/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.GradedSections.Cohomology
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.TwistedSections

/-!
# Degree-zero cohomology of associated twisted sections

Degree-zero cohomology of the tensor twists is transported from ordinary twisted global
sections. The resulting graded module restricts canonically to every lower-bounded family,
whose direct sum is then a module over the ambient graded algebra.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u v

namespace AlgebraicGeometry.Proj.TwistedSections.Cohomology

variable {R : Type v} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The degree-`n` cohomology group of the tensor twist of `F`. -/
@[stacks 01CV "degree-zero cohomology of an associated tensor twist"]
abbrev degree (F : (Proj 𝒜).Modules) (n : ℤ) : Type u :=
  GradedSections.Cohomology.degree 𝒜
    (ProjTwistFamily.tensorTwist
      (AssociatedModule.twistingSheaf (R := R) (A := A) 𝒜) F) n

/-- Degree-zero cohomology is canonically additively equivalent to ordinary twisted sections. -/
@[stacks 01CV "degree-zero cohomology as twisted sections"]
noncomputable abbrev sectionsEquiv (F : (Proj 𝒜).Modules) (n : ℤ) :
    degree 𝒜 F n ≃+ Integral.degree 𝒜 F n :=
  GradedSections.Cohomology.sectionsEquiv 𝒜
    (ProjTwistFamily.tensorTwist
      (AssociatedModule.twistingSheaf (R := R) (A := A) 𝒜) F) n

/-- Homogeneous multiplication on degree-zero cohomology is transported from twisted sections. -/
@[stacks 01CV "homogeneous action on twisted degree-zero cohomology"]
theorem degree_smul (F : (Proj 𝒜).Modules) {m : ℕ} {n : ℤ}
    (p : 𝒜 m) (x : degree 𝒜 F n) :
    GradedMonoid.GSMul.smul
        (A := fun d : ℕ ↦ 𝒜 d) (M := degree 𝒜 F) p x =
      (sectionsEquiv 𝒜 F ((m : ℤ) + n)).symm
        (Integral.smul 𝒜 F p (sectionsEquiv 𝒜 F n x)) := sorry

/-- The direct sum of tensor-twist cohomology groups in degrees bounded below by `k`. -/
@[stacks 01CV "lower-truncated twisted degree-zero cohomology"]
abbrev truncated (F : (Proj 𝒜).Modules) (k : ℤ) : Type u :=
  GradedSections.Cohomology.truncated 𝒜
    (ProjTwistFamily.tensorTwist
      (AssociatedModule.twistingSheaf (R := R) (A := A) 𝒜) F) k

/-- An ambient homogeneous scalar acts on a pure lower-bounded summand through the degree action. -/
@[stacks 01CV "homogeneous action on a pure truncated cohomology summand"]
theorem smul_of (F : (Proj 𝒜).Modules) (k : ℤ) {m : ℕ}
    (p : 𝒜 m) (d : {d : ℤ // k ≤ d}) (x : degree 𝒜 F d.1) :
    ((p : A) •
        DirectSum.of (DirectSum.Gmodule.LowerBound.pieces k (degree 𝒜 F)) d x :
      truncated 𝒜 F k) =
      DirectSum.of (DirectSum.Gmodule.LowerBound.pieces k (degree 𝒜 F)) (m +ᵥ d)
        (GradedMonoid.GSMul.smul
          (A := fun e : ℕ ↦ 𝒜 e) (M := degree 𝒜 F) p x) := sorry

end AlgebraicGeometry.Proj.TwistedSections.Cohomology
