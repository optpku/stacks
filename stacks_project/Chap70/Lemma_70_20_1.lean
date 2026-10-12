/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Topology.Defs.Basic
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-!
# Approximation of closed subsets after étale neighbourhoods

A quasi-compact morphism of algebraic spaces admits affine étale approximations of
closed subsets of a fibre product that avoid a given point of the base, after a
base change that is locally of finite presentation.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 70.20.1 (1): If `f : X ⟶ Y` is a quasi-compact morphism of algebraic
spaces over a scheme `S` and `g : Z ⟶ Y` is any morphism, then for a point `z`
of `Z` and a closed subset `T` of `Points (pullback f g)` whose image in
`Points Z` does not contain `z`, there is an étale neighbourhood `(V, v) ⟶ (Z, z)`
from an affine scheme, a commutative square `ofOverMap a` over `φ` and `g` with
`b : ofOver Z' ⟶ Y` locally of finite presentation from an affine scheme, and a
closed subset `T'` of `Points (pullbackAlongScheme f b)` such that `a(v)` is not
in the image of `T'` in `Points (ofOver Z')` and the inverse image of `T` in
`Points (pullbackAlongScheme f (φ ≫ g))` maps into `T'`. -/
@[stacks 0CM8]
theorem existsAffineEtaleApproximationAvoidingImage
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] (g : Z ⟶ Y) [HasPullback f g]
    (z : Points Z) (T : Set (Points (pullback f g)))
    {τ : TopologicalSpace (Points (pullback f g))}
    (hτ : IsPointsTopology (pullback f g) τ)
    (hT : @IsClosed (Points (pullback f g)) τ T)
    (hz : z ∉ Points.map (pullback.snd f g) '' T) :
    ∃ (V : Over S) (_ : IsAffine V.left)
      (φ : ofOver V ⟶ Z) (_ : Etale φ)
      (v : V.left) (_ : Points.map φ (ofOver.pointsEquiv V v) = z)
      (Z' : Over S) (_ : IsAffine Z'.left)
      (a : V ⟶ Z') (b : ofOver Z' ⟶ Y) (_ : LocallyOfFinitePresentation b)
      (_ : CommSq (ofOverMap a) φ b g)
      (T' : Set (Points (pullbackAlongScheme f b)))
      (_ : ∀ τ' : TopologicalSpace (Points (pullbackAlongScheme f b)),
        IsPointsTopology (pullbackAlongScheme f b) τ' →
          @IsClosed (Points (pullbackAlongScheme f b)) τ' T')
      (toXZ : pullbackAlongScheme f (φ ≫ g) ⟶ pullback f g)
      (toXZ' : pullbackAlongScheme f (φ ≫ g) ⟶ pullbackAlongScheme f b)
      (_ : toXZ ≫ pullback.fst f g = pullbackAlongScheme.fst f (φ ≫ g))
      (_ : toXZ ≫ pullback.snd f g = pullbackAlongScheme.snd f (φ ≫ g) ≫ φ)
      (_ : toXZ' ≫ pullbackAlongScheme.fst f b = pullbackAlongScheme.fst f (φ ≫ g))
      (_ : toXZ' ≫ pullbackAlongScheme.snd f b =
        pullbackAlongScheme.snd f (φ ≫ g) ≫ ofOverMap a),
      ofOver.pointsEquiv Z' (a.left v) ∉
          Points.map (pullbackAlongScheme.snd f b) '' T' ∧
        Points.map toXZ' '' (Points.map toXZ ⁻¹' T) ⊆ T' :=
  sorry

/-- Lemma 70.20.1 (2): If in addition `Z` is a scheme, then the étale neighbourhood
`V` in Lemma 70.20.1 (1) may be taken to be an affine open neighbourhood of `z`. -/
@[stacks 0CM8]
theorem existsAffineOpenApproximationAvoidingImage
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {W : Over S}
    (f : X ⟶ Y) [QuasiCompact f] (g : ofOver W ⟶ Y) [HasPullback f g]
    (z : W.left) (T : Set (Points (pullback f g)))
    {τ : TopologicalSpace (Points (pullback f g))}
    (hτ : IsPointsTopology (pullback f g) τ)
    (hT : @IsClosed (Points (pullback f g)) τ T)
    (hz : ofOver.pointsEquiv W z ∉ Points.map (pullback.snd f g) '' T) :
    ∃ (V : W.left.Opens) (hVz : z ∈ (V : Set W.left)) (_ : IsAffine V.toScheme)
      (φ : ofOver (Over.mk (V.ι ≫ W.hom)) ⟶ ofOver W)
      (_ : φ = ofOverMap (Over.homMk V.ι))
      (Z' : Over S) (_ : IsAffine Z'.left)
      (a : Over.mk (V.ι ≫ W.hom) ⟶ Z')
      (b : ofOver Z' ⟶ Y) (_ : LocallyOfFinitePresentation b)
      (_ : CommSq (ofOverMap a) φ b g)
      (T' : Set (Points (pullbackAlongScheme f b)))
      (_ : ∀ τ' : TopologicalSpace (Points (pullbackAlongScheme f b)),
        IsPointsTopology (pullbackAlongScheme f b) τ' →
          @IsClosed (Points (pullbackAlongScheme f b)) τ' T')
      (toXZ : pullbackAlongScheme f (φ ≫ g) ⟶ pullback f g)
      (toXZ' : pullbackAlongScheme f (φ ≫ g) ⟶ pullbackAlongScheme f b)
      (_ : toXZ ≫ pullback.fst f g = pullbackAlongScheme.fst f (φ ≫ g))
      (_ : toXZ ≫ pullback.snd f g = pullbackAlongScheme.snd f (φ ≫ g) ≫ φ)
      (_ : toXZ' ≫ pullbackAlongScheme.fst f b = pullbackAlongScheme.fst f (φ ≫ g))
      (_ : toXZ' ≫ pullbackAlongScheme.snd f b =
        pullbackAlongScheme.snd f (φ ≫ g) ≫ ofOverMap a),
      ofOver.pointsEquiv Z' (a.left ⟨z, hVz⟩) ∉
          Points.map (pullbackAlongScheme.snd f b) '' T' ∧
        Points.map toXZ' '' (Points.map toXZ ⁻¹' T) ⊆ T' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
