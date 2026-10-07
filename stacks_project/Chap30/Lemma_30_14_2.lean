module

import StacksCheckRecall
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.CoherentCohomology
import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Proper
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian
import ReasLib.RingTheory.GradedAlgebra.GeneratedBy

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)]

/- Lemma 30.14.2 (Noetherianity): if the degree-zero part is Noetherian and finitely many
degree-one elements generate the ring over it, then its projective spectrum is Noetherian. -/
@[stacks 0AG6] #check
  (fun (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) =>
    (AlgebraicGeometry.Scheme.Hom.FiniteType.isNoetherian
      (AlgebraicGeometry.Proj.toSpecZero 𝒜) : IsNoetherian (Proj 𝒜)))

variable (F : (Proj 𝒜).Modules) [F.IsCoherent]

/- Lemma 30.14.2 (1): every coherent module on this projective spectrum is a quotient of a
finite coproduct of canonical twisting sheaves. -/
@[stacks 0AG6] #check
  (fun (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) =>
    (AlgebraicGeometry.Proj.Coherent.exists_epi_from_twists
      (𝒜 := 𝒜)
      (hA := Algebra.FiniteType.isNoetherianRing (𝒜 0) A) F :
        ∃ (r : ℕ) (d : Fin r → ℤ)
          (π : (∐ fun j : Fin r ↦
            Proj.AssociatedModule.twistingSheaf 𝒜 (d j)) ⟶ F), Epi π))

variable (i : ℕ)

/- Lemma 30.14.2 (2): the cohomology of every coherent module is finite over the degree-zero
ring for the scalar action induced by the structure morphism. -/
@[stacks 0AG6] #check
  (fun (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) =>
    (AlgebraicGeometry.Scheme.Hom.cohomologyFinite
      (AlgebraicGeometry.Proj.toSpecZero 𝒜) F i :
        Module.Finite (𝒜 0) (Scheme.Hom.cohomology (Proj.toSpecZero 𝒜) F i)))

variable (hi : 0 < i)

/- Lemma 30.14.2 (3): positive-degree cohomology of sufficiently positive canonical tensor
twists of a coherent module vanishes. -/
@[stacks 0AG6] #check
  (fun (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) =>
    (AlgebraicGeometry.Proj.Coherent.twistCohomology_eventually_isZero
      (𝒜 := 𝒜)
      (hA := Algebra.FiniteType.isNoetherianRing (𝒜 0) A) F i hi :
        ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
          IsZero (Scheme.Hom.cohomology (Proj.toSpecZero 𝒜)
            (ProjTwistFamily.tensorTwist
              (Proj.AssociatedModule.twistingSheaf 𝒜) F d) i)))

variable (k : ℤ)

/- Lemma 30.14.2 (4): every truncation of the canonically acted-on graded module of global
sections of the tensor twists is finite over the graded ring. -/
@[stacks 0AG6] #check
  (fun (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1) =>
    (AlgebraicGeometry.Proj.Coherent.truncatedSections_finite
      (𝒜 := 𝒜)
      (hA := Algebra.FiniteType.isNoetherianRing (𝒜 0) A) F k :
        Module.Finite A (Proj.TwistedSections.Cohomology.truncated 𝒜 F k)))
