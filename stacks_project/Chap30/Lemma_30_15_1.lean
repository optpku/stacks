module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.CoherentCohomology

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
noncomputable section

universe u

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] [IsNoetherianRing A]

/- Lemma 30.15.1 (Noetherianity): the projective spectrum of a Noetherian graded ring is Noetherian. -/
@[stacks 0B5Q] #check
  (AlgebraicGeometry.Proj.instIsNoetherian 𝒜 :
    AlgebraicGeometry.IsNoetherian (Proj 𝒜))

variable (F : (Proj 𝒜).Modules) [F.IsCoherent]

/- Lemma 30.15.1 (1): every coherent module is a quotient of a finite coproduct of canonical
twisting sheaves. -/
@[stacks 0B5Q] #check
  (AlgebraicGeometry.Proj.Coherent.exists_epi_from_twists
    𝒜 F :
      ∃ (r : ℕ) (d : Fin r → ℤ)
        (π : (∐ fun j : Fin r ↦ Proj.AssociatedModule.twistingSheaf 𝒜 (d j)) ⟶ F), Epi π)

variable (i : ℕ)

/- Lemma 30.15.1 (2): cohomology is finite over the degree-zero ring for the scalar action
induced by the structure morphism. -/
@[stacks 0B5Q] #check
  (AlgebraicGeometry.Proj.Coherent.cohomology_finite 𝒜 F i :
    Module.Finite (𝒜 0) (Scheme.Hom.cohomology (Proj.toSpecZero 𝒜) F i))

variable (hi : 0 < i)

/- Lemma 30.15.1 (3): positive-degree cohomology of sufficiently positive canonical tensor
twists vanishes. -/
@[stacks 0B5Q] #check
  (AlgebraicGeometry.Proj.Coherent.twistCohomology_eventually_isZero
    𝒜 F i hi :
      ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
        IsZero (Scheme.Hom.cohomology (Proj.toSpecZero 𝒜)
          (ProjTwistFamily.tensorTwist (Proj.AssociatedModule.twistingSheaf 𝒜) F d) i))

variable (k : ℤ)

/- Lemma 30.15.1 (4): every truncation of the canonically acted-on graded module of global
sections of the canonical tensor twists is finite over the graded ring. -/
@[stacks 0B5Q] #check
  (AlgebraicGeometry.Proj.Coherent.truncatedSections_finite
    𝒜 F k :
      Module.Finite A
        (Proj.TwistedSections.Cohomology.truncated 𝒜 F k))
