module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Correspondence

/-! # Descent of open subspaces along fpqc coverings -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.FpqcCovering

/-- Compatible open subspaces on an fpqc covering family determine a unique
open set of points of the target whose preimage on each member is its given
open subspace's point-set. -/
theorem existsUnique_open {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over T} (hfamily : FpqcCovering family)
    (W : (i : ι) → OpenSubspace (family i).left)
    (hcompat : ∀ i j : ι,
      ((W i).inverseImage (pullback.fst (family i).hom (family j).hom)).pointsSet =
        ((W j).inverseImage (pullback.snd (family i).hom (family j).hom)).pointsSet) :
    ∃! V : Opens (Points T),
      ∀ i : ι,
        (W i).pointsSet =
          Points.map (family i).hom ⁻¹' V.carrier :=
  sorry

/-- Compatible open subspaces on an fpqc covering family arise as inverse images
of an open subspace of the target, unique up to unique lift over the target. -/
theorem existsUnique_openSubspace {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over T} (hfamily : FpqcCovering family)
    (W : (i : ι) → OpenSubspace (family i).left)
    (hcompat : ∀ i j : ι,
      ((W i).inverseImage (pullback.fst (family i).hom (family j).hom)).pointsSet =
        ((W j).inverseImage (pullback.snd (family i).hom (family j).hom)).pointsSet) :
    ∃ U : OpenSubspace T,
      (∀ i : ι,
          (W i).pointsSet = (U.inverseImage (family i).hom).pointsSet) ∧
        ∀ U' : OpenSubspace T,
          (∀ i : ι,
              (W i).pointsSet = (U'.inverseImage (family i).hom).pointsSet) →
            ∃! φ : U'.X ⟶ U.X, φ ≫ U.ι = U'.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FpqcCovering
