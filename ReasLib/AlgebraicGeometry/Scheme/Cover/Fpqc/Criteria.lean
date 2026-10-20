module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc

/-!
# Local criteria for fpqc covering families

This leaf separates the local image-cover conditions that occur in equivalent
characterizations of fpqc covers.  The canonical topology owner remains
`Scheme.FpqcCovering`; the predicates below are deliberately fine-grained so
they can also be reused in arguments about local refinements.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme
namespace Fpqc
namespace Criterion

variable {T : Scheme.{u}} {ι : Type v}

/-- A family of quasi-compact opens in the members of `X` has image exactly
the open subset `U` of the target. -/
def imageCover (X : ι → Over T) (U : T.Opens) : Prop :=
  ∃ V : (i : ι) → (X i).left.Opens,
    Set.Finite {i : ι | V i ≠ ⊥} ∧
      (∀ i : ι, IsCompact (V i : Set (X i).left)) ∧
        (⋃ i : ι, (X i).hom.base '' (V i : Set (X i).left)) = (U : Set T)

/-- Every member of an indexed family over `T` is flat. -/
def pointwiseFlat (X : ι → Over T) : Prop :=
  ∀ i : ι, Flat (X i).hom

/-- The local image-cover condition on every affine open of the target. -/
def Affine (X : ι → Over T) : Prop :=
  pointwiseFlat X ∧
    ∀ U : T.Opens, IsAffineOpen U → imageCover X U

/-- A family satisfying the affine criterion is pointwise flat. -/
theorem Affine.flat {X : ι → Over T} (hX : Affine X) (i : ι) :
    Flat (X i).hom := sorry

/-- The affine criterion supplies an image cover of every affine target
open. -/
theorem Affine.imageCover {X : ι → Over T} (hX : Affine X)
    (U : T.Opens) (hU : IsAffineOpen U) :
    imageCover X U := sorry

/-- The local image-cover criterion checked on one affine open cover of the
target. -/
def Refinement (X : ι → Over T) : Prop :=
  pointwiseFlat X ∧
    ∃ 𝒰 : Scheme.AffineOpenCover.{u} T,
      ∀ a : 𝒰.I₀, imageCover X ((𝒰.f a).opensRange)

/-- A family satisfying the affine-cover refinement criterion is pointwise
flat. -/
theorem Refinement.flat {X : ι → Over T} (hX : Refinement X) (i : ι) :
    Flat (X i).hom := sorry

/-- The refinement criterion supplies an affine open cover with an image
cover on every member. -/
theorem Refinement.cover {X : ι → Over T} (hX : Refinement X) :
    ∃ 𝒰 : Scheme.AffineOpenCover.{u} T,
      ∀ a : 𝒰.I₀, imageCover X ((𝒰.f a).opensRange) := sorry

/-- The local image-cover condition in a neighborhood of one target point. -/
def neighborhoodCover (X : ι → Over T) (t : T) : Prop :=
  ∃ V : (i : ι) → (X i).left.Opens,
    Set.Finite {i : ι | V i ≠ ⊥} ∧
      (∀ i : ι, IsCompact (V i : Set (X i).left)) ∧
        ∃ W : T.Opens,
          t ∈ (W : Set T) ∧
            (W : Set T) ⊆
              ⋃ i : ι, (X i).hom.base '' (V i : Set (X i).left)

/-- The pointwise local image-cover criterion. -/
def Neighborhood (X : ι → Over T) : Prop :=
  pointwiseFlat X ∧ ∀ t : T, neighborhoodCover X t

/-- A family satisfying the neighborhood criterion is pointwise flat. -/
theorem Neighborhood.flat {X : ι → Over T} (hX : Neighborhood X) (i : ι) :
    Flat (X i).hom := sorry

/-- The neighborhood criterion supplies a local image cover at every target
point. -/
theorem Neighborhood.atPoint {X : ι → Over T} (hX : Neighborhood X) (t : T) :
    neighborhoodCover X t := sorry

/-- The canonical fpqc-covering predicate is characterized by the affine
local image-cover criterion. -/
theorem cover_iff_affine (X : ι → Over T) :
    FpqcCovering X ↔ Affine X := sorry

/-- The affine local criterion is equivalent to the affine-cover refinement
criterion. -/
theorem affine_iff_refinement (X : ι → Over T) :
    Affine X ↔ Refinement X := sorry

/-- On a quasi-separated target, the affine local criterion is equivalent to
the pointwise neighborhood criterion. -/
theorem affine_iff_neighborhood (X : ι → Over T) [QuasiSeparatedSpace T] :
    Affine X ↔ Neighborhood X := sorry

end Criterion
end Fpqc
end AlgebraicGeometry.Scheme
