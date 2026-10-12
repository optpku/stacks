/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u v

section

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Lemma 27.8.10

The scheme `Proj(S)` has the canonical morphism `Proj(S) ⟶ Spec(S₀)`, and on points this
morphism sends a homogeneous prime ideal to its contraction along the degree-zero inclusion.
-/
@[stacks 01ME] #check
  (AlgebraicGeometry.Proj.toSpecZero_base_asIdeal (𝒜 := 𝒜) :
    ∀ x : ProjectiveSpectrum 𝒜,
      ((AlgebraicGeometry.Proj.toSpecZero 𝒜).base x).asIdeal =
        Ideal.comap (algebraMap (𝒜 0) A) x.asHomogeneousIdeal.toIdeal)

#check
  (AlgebraicGeometry.Proj.toSpecZero 𝒜 : Proj 𝒜 ⟶ Spec (CommRingCat.of (𝒜 0)))

end
