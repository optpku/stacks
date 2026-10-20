module

public import ReasLib.Algebra.Module.Graded.Decomposition
public import ReasLib.Algebra.Module.Graded.LowerBound
public import ReasLib.Algebra.Module.Graded.Reindex
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.GradedSections
public import ReasLib.CategoryTheory.Sites.Cohomology.Zero

/-!
# Degree-zero cohomology of graded twist families

For an arbitrary integer-indexed family of module sheaves on a projective spectrum, degree-zero
cohomology is transported from ordinary sections. Any graded action on those sections therefore
induces canonical actions on the cohomology degrees and all of their lower truncations.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u v

namespace AlgebraicGeometry.Proj.GradedSections.Cohomology

variable {R : Type v} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
variable (twist : ℤ → (Proj 𝒜).Modules)

/-- The degree-`n` degree-zero cohomology group of an arbitrary twist family. -/
@[stacks 01CV "degree-zero cohomology of a graded twist family"]
abbrev degree (n : ℤ) : Type u :=
  (RingedSpace.moduleCohomology (twist n) 0 : Type u)

/-- Degree-zero cohomology is canonically additively equivalent to ordinary sections. -/
@[stacks 01CV "degree-zero cohomology as sections of a twist family"]
noncomputable def sectionsEquiv (n : ℤ) :
    degree 𝒜 twist n ≃+ Γ(twist n, ⊤) :=
  CategoryTheory.Sheaf.cohomologyZeroEquivSections
    (Opens.grothendieckTopology (Proj 𝒜).carrier)
    ((SheafOfModules.toSheaf (Proj 𝒜).toRingedSpace.ringCatSheaf).obj (twist n))
    (⊤ : (Proj 𝒜).Opens)

/-- The direct sum of twist-family cohomology groups in degrees bounded below by `k`. -/
@[stacks 01CV "lower-truncated degree-zero cohomology of a twist family"]
abbrev truncated (k : ℤ) : Type u :=
  truncatedTwistGlobalSections 𝒜 twist k

section Graded

variable [DirectSum.Gmodule (fun m : ℕ ↦ 𝒜 m) (fun n : ℤ ↦ Γ(twist n, ⊤))]

/-- The graded module on degree-zero cohomology transported from the action on sections. -/
@[reducible, stacks 01CV "transported graded module on degree-zero twist cohomology"]
noncomputable def gmodule :
    DirectSum.Gmodule (fun m : ℕ ↦ 𝒜 m) (degree 𝒜 twist) :=
  DirectSum.Gmodule.ofAddEquiv
    (M := fun n : ℤ ↦ Γ(twist n, ⊤)) (N := degree 𝒜 twist)
    (fun n ↦ (sectionsEquiv 𝒜 twist n).symm)

/-- Degree-zero twist cohomology carries the canonical transported graded-module structure. -/
@[stacks 01CV "canonical graded module on degree-zero twist cohomology"]
noncomputable instance instGmodule :
    DirectSum.Gmodule (fun m : ℕ ↦ 𝒜 m) (degree 𝒜 twist) :=
  gmodule 𝒜 twist

/-- Homogeneous multiplication on cohomology is transported through the section equivalences. -/
@[stacks 01CV "homogeneous action on degree-zero twist cohomology"]
theorem degree_smul {m : ℕ} {n : ℤ}
    (p : 𝒜 m) (x : degree 𝒜 twist n) :
    GradedMonoid.GSMul.smul
        (A := fun d : ℕ ↦ 𝒜 d) (M := degree 𝒜 twist) p x =
      (sectionsEquiv 𝒜 twist (m +ᵥ n)).symm
        (GradedMonoid.GSMul.smul
          (A := fun d : ℕ ↦ 𝒜 d) (M := fun d : ℤ ↦ Γ(twist d, ⊤))
          p (sectionsEquiv 𝒜 twist n x)) := sorry

/-- Lower-bounded cohomology carries the canonical reindexed graded-module structure. -/
@[stacks 01CV "canonical lower-bound graded module on degree-zero twist cohomology"]
noncomputable instance instTruncatedGmodule (k : ℤ) :
    DirectSum.Gmodule (fun m : ℕ ↦ 𝒜 m)
      (DirectSum.Gmodule.LowerBound.pieces k (degree 𝒜 twist)) :=
  DirectSum.Gmodule.LowerBound.instGmodule
    (fun m : ℕ ↦ 𝒜 m) (degree 𝒜 twist) k

/-- The ambient graded algebra acts canonically on lower-truncated twist cohomology. -/
@[stacks 01CV "module on lower-truncated degree-zero twist cohomology"]
noncomputable instance instModule (k : ℤ) :
    Module A (truncated 𝒜 twist k) :=
  DirectSum.Gmodule.moduleOfDecomposition 𝒜
    (DirectSum.Gmodule.LowerBound.pieces k (degree 𝒜 twist))

/-- An ambient homogeneous scalar acts on a pure lower-bounded summand through the degree action. -/
@[stacks 01CV "homogeneous action on a pure truncated twist-cohomology summand"]
theorem smul_of (k : ℤ) {m : ℕ}
    (p : 𝒜 m) (d : {d : ℤ // k ≤ d}) (x : degree 𝒜 twist d.1) :
    ((p : A) •
        DirectSum.of (DirectSum.Gmodule.LowerBound.pieces k (degree 𝒜 twist)) d x :
      truncated 𝒜 twist k) =
      DirectSum.of (DirectSum.Gmodule.LowerBound.pieces k (degree 𝒜 twist)) (m +ᵥ d)
        (GradedMonoid.GSMul.smul
          (A := fun e : ℕ ↦ 𝒜 e) (M := degree 𝒜 twist) p x) := sorry

end Graded

end AlgebraicGeometry.Proj.GradedSections.Cohomology
