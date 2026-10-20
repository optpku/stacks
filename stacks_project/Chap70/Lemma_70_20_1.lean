/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Approximation
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 70.20.1: Affine étale approximation of a closed subset avoiding a fibre. -/
@[stacks 0CM8] #check (AlgebraicGeometry.AlgebraicSpace.existsAffineEtaleApproximationAvoidingImage :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] (g : Z ⟶ Y)
    (z : Points Z) (T : Set (Points (pullback f g)))
    (hT : IsClosed T)
    (hz : z ∉ Points.map (pullback.snd f g) '' T),
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
        Points.map toXZ' '' (Points.map toXZ ⁻¹' T) ⊆ T')

#check (AlgebraicGeometry.AlgebraicSpace.existsAffineOpenApproximationAvoidingImage :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {W : Over S}
    (f : X ⟶ Y) [QuasiCompact f] (g : ofOver W ⟶ Y)
    (z : W.left) (T : Set (Points (pullback f g)))
    (hT : IsClosed T)
    (hz : ofOver.pointsEquiv W z ∉ Points.map (pullback.snd f g) '' T),
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
        Points.map toXZ' '' (Points.map toXZ ⁻¹' T) ⊆ T')

end AlgebraicGeometry.AlgebraicSpace
