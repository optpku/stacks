module

public import ReasLib.AlgebraicGeometry.Scheme.StandardZariskiCover.AffineOpen

/-!
# Standard-open refinements of affine-open covers

`StandardZariskiCover.OnAffineOpen` owns the finite distinguished-open cover of
one affine open. This file records the additional explicit data exhibiting
such a cover as a refinement of an ambient affine-open cover.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.AffineOpenCover

/-- Explicit data exhibiting a finite standard-open cover of `V` as a refinement of `𝒰`. -/
@[stacks 01IX "standard-open refinement data"]
structure StandardRefinement {X : Scheme.{u}} (𝒰 : X.AffineOpenCover.{v})
    (V : X.affineOpens) where
  /-- The finite standard-open cover of `V`. -/
  cover : StandardZariskiCover.OnAffineOpen.{u, w} X V
  /-- The member of `𝒰` containing each member of the standard-open cover. -/
  toIndex : cover.index → 𝒰.I₀
  /-- A section on the chosen member of `𝒰` which defines each standard open. -/
  ambientSection : (i : cover.index) → Γ(X, (𝒰.f (toIndex i)).opensRange)
  /-- Each member of the standard-open cover is the basic open of its chosen ambient section. -/
  affineOpen_eq_basicOpen : ∀ i,
    (cover.affineOpen i : X.Opens) = X.basicOpen (ambientSection i)

namespace StandardRefinement

variable {X : Scheme.{u}} {𝒰 : X.AffineOpenCover.{v}} {V : X.affineOpens}

/-- The members of a standard refinement cover the original affine open. -/
@[stacks 01IX "standard-open refinement supremum"]
theorem iSup_affineOpen_eq (R : StandardRefinement 𝒰 V) :
    (⨆ i : R.cover.index, (R.cover.affineOpen i : X.Opens)) = (V : X.Opens) := sorry

/-- Each member of a standard refinement lies in its chosen member of the ambient cover. -/
@[stacks 01IX "standard-open refinement containment"]
theorem affineOpen_le_opensRange (R : StandardRefinement 𝒰 V) (i : R.cover.index) :
    (R.cover.affineOpen i : X.Opens) ≤ (𝒰.f (R.toIndex i)).opensRange := sorry

/-- The covering, containment, and basic-open equations exposed by a standard refinement. -/
@[stacks 01IX "standard-open refinement specification"]
theorem spec (R : StandardRefinement 𝒰 V) :
    (⨆ i : R.cover.index, (R.cover.affineOpen i : X.Opens)) = (V : X.Opens) ∧
      (∀ i, (R.cover.affineOpen i : X.Opens) ≤
        (𝒰.f (R.toIndex i)).opensRange) ∧
      ∀ i, (R.cover.affineOpen i : X.Opens) = X.basicOpen (R.ambientSection i) := sorry

end StandardRefinement

/-- Lemma 26.11.6: every affine open admits a finite standard-open refinement of any chosen
affine-open cover of the ambient scheme. -/
@[stacks 01IX]
theorem exists_standardRefinement {X : Scheme.{u}} (𝒰 : X.AffineOpenCover.{v})
    (V : X.affineOpens) :
    Nonempty (StandardRefinement.{u, v, w} 𝒰 V) := sorry

end AlgebraicGeometry.Scheme.AffineOpenCover
