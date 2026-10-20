module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Affine approximation of closed subsets of algebraic-space fibre products

Closed subsets avoiding a fibre of a quasi-compact morphism admit affine,
locally finitely presented approximations after an affine étale base change.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a quasi-compact morphism of algebraic spaces, a closed subset of a fibre
product whose image avoids a given point admits an affine, locally finitely
presented approximation after passing to an affine étale neighbourhood of that
point. The approximating closed subset avoids the image of the chosen point and
contains the image of the inverse image of the original subset. -/
theorem existsAffineEtaleApproximationAvoidingImage
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] (g : Z ⟶ Y)
    (z : Points Z) (T : Set (Points (pullback f g)))
    (hT : IsClosed T)
    (hz : z ∉ Points.map (pullback.snd f g) '' T) :
    ∃ (V : Over S) (_ : IsAffine V.left)
      (φ : ofOver V ⟶ Z) (_ : Etale φ)
      (v : V.left) (_ : Points.map φ (ofOver.pointsEquiv V v) = z)
      (Z' : Over S) (_ : IsAffine Z'.left)
      (a : V ⟶ Z') (b : ofOver Z' ⟶ Y) (_ : LocallyOfFinitePresentation b)
      (_ : CommSq (ofOverMap a) φ b g)
      (T' : Set (Points (pullback f b)))
      (_ : IsClosed T')
      (toXZ : pullback f (φ ≫ g) ⟶ pullback f g)
      (toXZ' : pullback f (φ ≫ g) ⟶ pullback f b)
      (_ : toXZ ≫ pullback.fst f g = pullback.fst f (φ ≫ g))
      (_ : toXZ ≫ pullback.snd f g = pullback.snd f (φ ≫ g) ≫ φ)
      (_ : toXZ' ≫ pullback.fst f b = pullback.fst f (φ ≫ g))
      (_ : toXZ' ≫ pullback.snd f b =
        pullback.snd f (φ ≫ g) ≫ ofOverMap a),
      ofOver.pointsEquiv Z' (a.left v) ∉
          Points.map (pullback.snd f b) '' T' ∧
        Points.map toXZ' '' (Points.map toXZ ⁻¹' T) ⊆ T' :=
  sorry

/-- For a quasi-compact morphism of algebraic spaces and a base change by a
scheme, a closed subset avoiding a given fibre admits an affine, locally finitely
presented approximation on an affine open neighbourhood of the chosen scheme
point. The approximating closed subset avoids the corresponding point and
contains the image of the restricted original subset. -/
theorem existsAffineOpenApproximationAvoidingImage
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {W : Over S}
    (f : X ⟶ Y) [QuasiCompact f] (g : ofOver W ⟶ Y)
    (z : W.left) (T : Set (Points (pullback f g)))
    (hT : IsClosed T)
    (hz : ofOver.pointsEquiv W z ∉ Points.map (pullback.snd f g) '' T) :
    ∃ (V : W.left.Opens) (hVz : z ∈ (V : Set W.left)) (_ : IsAffine V.toScheme)
      (φ : ofOver (Over.mk (V.ι ≫ W.hom)) ⟶ ofOver W)
      (_ : φ = ofOverMap (Over.homMk V.ι))
      (Z' : Over S) (_ : IsAffine Z'.left)
      (a : Over.mk (V.ι ≫ W.hom) ⟶ Z')
      (b : ofOver Z' ⟶ Y) (_ : LocallyOfFinitePresentation b)
      (_ : CommSq (ofOverMap a) φ b g)
      (T' : Set (Points (pullback f b)))
      (_ : IsClosed T')
      (toXZ : pullback f (φ ≫ g) ⟶ pullback f g)
      (toXZ' : pullback f (φ ≫ g) ⟶ pullback f b)
      (_ : toXZ ≫ pullback.fst f g = pullback.fst f (φ ≫ g))
      (_ : toXZ ≫ pullback.snd f g = pullback.snd f (φ ≫ g) ≫ φ)
      (_ : toXZ' ≫ pullback.fst f b = pullback.fst f (φ ≫ g))
      (_ : toXZ' ≫ pullback.snd f b =
        pullback.snd f (φ ≫ g) ≫ ofOverMap a),
      ofOver.pointsEquiv Z' (a.left ⟨z, hVz⟩) ∉
          Points.map (pullback.snd f b) '' T' ∧
        Points.map toXZ' '' (Points.map toXZ ⁻¹' T) ⊆ T' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
