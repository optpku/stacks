/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology

/-!
# Truncated graded sections on projective spectra

This leaf owns the direct-sum carrier formed from degree-zero cohomology of an
arbitrary integer-indexed family of modules on `Proj`.  It deliberately does
not assume that the family is supplied by tensor powers of an invertible
module, so it applies equally to externally specified twist families.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.Proj

/-- The truncated graded group `⨁_{d ≥ k} H^0(Proj 𝒜, twist d)` for an arbitrary chosen family
of module-sheaf twists on `Proj 𝒜`. -/
abbrev truncatedTwistGlobalSections
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (twist : ℤ → (Proj 𝒜).Modules) (k : ℤ) : Type u :=
  DirectSum {d : ℤ // k ≤ d} fun d ↦
    (RingedSpace.moduleCohomology (X := (Proj 𝒜).toRingedSpace) (twist d.1) 0 : Type u)

end AlgebraicGeometry.Proj
