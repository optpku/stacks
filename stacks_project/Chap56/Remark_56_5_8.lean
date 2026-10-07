module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import stacks_project.Chap56.Lemma_56_5_2
public import stacks_project.Chap56.Lemma_56_5_5
public import stacks_project.Chap56.Remark_56_5_8_AffineOpenCoproductLinear

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))

/-- Remark 56.5.8 (1): every Fourier–Mukai functor (56.5.1.1) associated to a
quasi-coherent kernel on `Limits.pullback x y` is affine-open coproduct-linear. -/
@[stacks 0GPB]
instance fourierMukai_affineOpenCoproductLinear
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (K : Scheme.QCoh (Limits.pullback x y)) :
    AffineOpenCoproductLinear x y (fourierMukai x y K) := sorry

/-- Remark 56.5.8 (2): if `X` is quasi-compact with affine diagonal, the
hypotheses of `AffineOpenCoproductLinear` are enough to construct a comparison
`t : F ⟶ fourierMukai x y K` as in Lemma 56.5.5 and to show that `t` is an
isomorphism. -/
@[stacks 0GPB]
theorem exists_fourierMukai_iso_of_affineOpenCoproductLinear
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) [AffineOpenCoproductLinear x y F] :
    ∃ (K : Scheme.QCoh (Limits.pullback x y)) (t : F ⟶ fourierMukai x y K),
      IsIso t := sorry

/-- The functor sending a quasi-coherent kernel on `Limits.pullback x y` to the
associated Fourier–Mukai functor of (56.5.1.1), viewed as an affine-open
coproduct-linear functor. -/
@[stacks 0GPB]
def affineOpenFourierMukai
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] :
    Scheme.QCoh (Limits.pullback x y) ⥤ AffineOpenCoproductLinearFunctor x y where
  obj K := ⟨fourierMukai x y K, inferInstance⟩
  map {K K'} α :=
    ObjectProperty.homMk
      (Functor.whiskerLeft (Scheme.QCoh.pullback (Limits.pullback.fst x y))
        (Functor.whiskerRight (tensorRightHom α)
          (Scheme.QCoh.pushforward (Limits.pullback.snd x y))))
  map_id := sorry
  map_comp := sorry

/-- The underlying functor of `affineOpenFourierMukai` is the Fourier–Mukai
functor of (56.5.1.1). -/
theorem affineOpenFourierMukai_obj
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (K : Scheme.QCoh (Limits.pullback x y)) :
    ((affineOpenFourierMukai x y).obj K).obj = fourierMukai x y K := sorry

/-- Remark 56.5.8 (3): if `X` is quasi-compact with affine diagonal, the functors
(56.5.1.1) associated to quasi-coherent modules on `X ×_R Y` are exactly the
`R`-linear coproduct-preserving functors `F : Scheme.QCoh X ⥤ Scheme.QCoh Y`
such that `F ∘ j_*` is right exact for every affine open immersion `j : U ⟶ X`
and `F` preserves exactness of short exact sequences that split on every stalk. -/
@[stacks 0GPB]
theorem affineOpenFourierMukai_isEquivalence
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] :
    (affineOpenFourierMukai x y).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.QCoh
