module

public import ReasLib.AlgebraicGeometry.Scheme.BeauvilleLaszlo
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage

/-!
# Étale locality of glueable global sections

For a Beauville-Laszlo glueing pair, glueability on an affine étale covering
is equivalent to glueability on every affine étale test scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a Beauville-Laszlo glueing pair, an algebraic space over `Spec R`
admits an étale covering by affine schemes with glueable global sections if
and only if every affine scheme étale over it has glueable global sections. -/
@[stacks 0F9P]
theorem exists_affineEtale_glueableGlobalSections_iff
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] (f : R)
    [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f]
    (Y : AlgebraicSpace (Spec (CommRingCat.of R))) :
    (∃ (I : Type u) (hsmall : Small.{u} I)
        (U : I → Over (Spec (CommRingCat.of R)))
        (φ : ∀ i, ofOver (U i) ⟶ Y),
      (∀ i, AlgebraicGeometry.IsAffine (U i).left) ∧
        EtaleCovering (fun i ↦ Over.mk (φ i)) ∧
        ∀ i, Scheme.Hom.glueableGlobalSections R' f (U i)) ↔
      ∀ {T : Over (Spec (CommRingCat.of R))} [AlgebraicGeometry.IsAffine T.left]
        (φ : ofOver T ⟶ Y) [Etale φ],
        Scheme.Hom.glueableGlobalSections R' f T :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
