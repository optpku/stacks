module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.TwistedSections.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-!
# Coherent cohomology on projective spectra

This file records Noetherianity, finite presentations by canonical twisting sheaves, and
finiteness and vanishing results for coherent cohomology over arbitrary Noetherian graded rings.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.Proj

variable {R : Type v} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The projective spectrum of a Noetherian graded ring is a Noetherian scheme. -/
@[stacks 0B5Q "Noetherian projective spectrum"]
instance instIsNoetherian [hA : IsNoetherianRing A] :
    AlgebraicGeometry.IsNoetherian (Proj 𝒜) := sorry

namespace Coherent

/-- A coherent module on the projective spectrum of a Noetherian graded ring is a quotient of
a finite coproduct of canonical twisting sheaves. -/
@[stacks 0AG6, stacks 0B5Q "finite presentation of a coherent module by twists"]
theorem exists_epi_from_twists
    [hA : IsNoetherianRing A]
    (F : (Proj 𝒜).Modules) [F.IsCoherent] :
    ∃ (r : ℕ) (d : Fin r → ℤ)
      (π : (∐ fun j : Fin r ↦ AssociatedModule.twistingSheaf 𝒜 (d j)) ⟶ F), Epi π := sorry

/-- Cohomology of a coherent module on the projective spectrum of a Noetherian graded ring is
finite over the degree-zero ring for the action induced by the structure morphism. -/
@[stacks 0AG6, stacks 0B5Q "finiteness of coherent cohomology on a projective spectrum"]
theorem cohomology_finite
    [hA : IsNoetherianRing A]
    (F : (Proj 𝒜).Modules) [F.IsCoherent] (i : ℕ) :
    Module.Finite (𝒜 0) (Scheme.Hom.cohomology (Proj.toSpecZero 𝒜) F i) := sorry

/-- In every positive degree, cohomology of sufficiently positive canonical tensor twists of a
coherent module on the projective spectrum of a Noetherian graded ring vanishes. -/
@[stacks 0AG6, stacks 0B5Q "eventual vanishing of positive coherent twist cohomology"]
theorem twistCohomology_eventually_isZero
    [hA : IsNoetherianRing A]
    (F : (Proj 𝒜).Modules) [F.IsCoherent] (i : ℕ) (hi : 0 < i) :
    ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
      IsZero (Scheme.Hom.cohomology (Proj.toSpecZero 𝒜)
        (ProjTwistFamily.tensorTwist (AssociatedModule.twistingSheaf 𝒜) F d) i) := sorry

/-- Every truncation of canonically acted-on global sections of the tensor twists of a coherent
module on the projective spectrum of a Noetherian graded ring is finite over the graded ring. -/
@[stacks 0AG6, stacks 0B5Q "finiteness of truncated coherent twist sections"]
theorem truncatedSections_finite
    [hA : IsNoetherianRing A]
    (F : (Proj 𝒜).Modules) [F.IsCoherent] (k : ℤ) :
    Module.Finite A (TwistedSections.Cohomology.truncated 𝒜 F k) := sorry

end Coherent

end AlgebraicGeometry.Proj
