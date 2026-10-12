/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.AffineSpace
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap79.«79_12_0_2_FinitePart»

/-!
# Doubled-origin fold as a morphism of algebraic spaces

The fold from the affine line with doubled origin onto `A¹_k`, viewed as a
morphism of algebraic spaces over `Spec k`, together with the two origins in
the fibre over `0` and the four finite-part points they determine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable (k : Type u) [Field k]

/-- The base scheme `Spec k`. -/
abbrev base : Scheme.{u} :=
  Spec (CommRingCat.of k)

/-- The affine line `A¹_k`, as a scheme over `Spec k`. -/
abbrev affineLineOver : Over (base k) :=
  Over.mk (PuncturedAffineSpace.toBase (ULift.{u} (Fin 1)) k)

/-- The affine line with doubled origin, as a scheme over `Spec k`. -/
abbrev doubledOver : Over (base k) :=
  Over.mk (DoubledOrigin.toBase k 1)

/-- The fold of the doubled origin is a morphism over `Spec k`. -/
theorem foldOver_w :
    DoubledOrigin.fold k 1 ≫ (affineLineOver k).hom = (doubledOver k).hom :=
  sorry

/-- The fold `X ⟶ Y` as a morphism of schemes over `Spec k`. -/
def foldOver : doubledOver k ⟶ affineLineOver k :=
  Over.homMk (DoubledOrigin.fold k 1) (foldOver_w k)

/-- The underlying scheme morphism of `foldOver` is the doubled-origin fold. -/
theorem foldOver_left : (foldOver k).left = DoubledOrigin.fold k 1 :=
  sorry

/-- The fold `X ⟶ Y` as a morphism of algebraic spaces over `Spec k`. -/
def foldMorphism : ofOver (doubledOver k) ⟶ ofOver (affineLineOver k) :=
  ofOverMap (foldOver k)

/-- `foldMorphism` is `ofOverMap` of the scheme-level fold. -/
theorem foldMorphism_eq : foldMorphism k = ofOverMap (foldOver k) :=
  sorry

/-- The origin `Spec k` of the affine line, as a scheme over `Spec k`. -/
abbrev originOver : Over (base k) :=
  Over.mk (𝟙 (base k))

/-- The zero section of `A¹_k` is a morphism `Spec k ⟶ A¹_k` over `Spec k`. -/
def zeroSectionOver : originOver k ⟶ affineLineOver k :=
  Over.homMk (PuncturedAffineSpace.zeroSection (ULift.{u} (Fin 1)) k)
    (PuncturedAffineSpace.zeroSection_toBase (ULift.{u} (Fin 1)) k)

/-- The underlying scheme morphism of `zeroSectionOver` is the zero section. -/
theorem zeroSectionOver_left :
    (zeroSectionOver k).left =
      PuncturedAffineSpace.zeroSection (ULift.{u} (Fin 1)) k :=
  sorry

/-- The zero section `Spec k ⟶ Y` as a morphism of algebraic spaces over `Spec k`. -/
def originToY : ofOver (originOver k) ⟶ ofOver (affineLineOver k) :=
  ofOverMap (zeroSectionOver k)

/-- `originToY` is `ofOverMap` of the zero section. -/
theorem originToY_eq : originToY k = ofOverMap (zeroSectionOver k) :=
  sorry

/-- The scheme morphism `Spec k ⟶ X` selecting the origin in the `i`-th chart. -/
def originSchemeHom (i : Fin 2) :
    (originOver k).left ⟶ (doubledOver k).left :=
  PuncturedAffineSpace.zeroSection (ULift.{u} (Fin 1)) k ≫
    DoubledOrigin.chartMap k 1 i

/-- Each chart origin is a morphism over `Spec k`. -/
theorem originSchemeHom_w (i : Fin 2) :
    originSchemeHom k i ≫ (doubledOver k).hom = (originOver k).hom :=
  sorry

/-- The origin in the `i`-th chart, as a morphism of schemes over `Spec k`. -/
def originOverHom (i : Fin 2) : originOver k ⟶ doubledOver k :=
  Over.homMk (originSchemeHom k i) (originSchemeHom_w k i)

/-- The origin in the `i`-th chart, as a morphism of algebraic spaces over `Spec k`. -/
def originSection (i : Fin 2) :
    ofOver (originOver k) ⟶ ofOver (doubledOver k) :=
  ofOverMap (originOverHom k i)

/-- Folding the `i`-th origin recovers the zero section of `A¹_k`. -/
theorem originSection_comp_fold (i : Fin 2) :
    originSection k i ≫ foldMorphism k = originToY k :=
  sorry

/-- The triangle presenting the `i`-th origin as a point of the fibre over `0`. -/
theorem originToFibre_w (i : Fin 2) :
    𝟙 (ofOver (originOver k)) ≫ originToY k =
      originSection k i ≫ foldMorphism k :=
  sorry

/-- The morphism `Spec k ⟶ Spec k ×_Y X` selecting the `i`-th origin in the fibre. -/
def originToFibre (i : Fin 2) :
    ofOver (originOver k) ⟶ pullback (originToY k) (foldMorphism k) :=
  pullback.lift (𝟙 (ofOver (originOver k))) (originSection k i)
    (originToFibre_w k i)

/-- The unique point of `Spec k`, as a point of the algebraic space `ofOver originOver`. -/
def originClosedPoint : Points (ofOver (originOver k)) :=
  Points.mk (FieldValuedPoint.of k (originOver k).hom (𝟙 _))

/-- The point `0ᵢ` of the fibre `Spec k ×_Y X`. -/
def originPoint (i : Fin 2) :
    Points (pullback (originToY k) (foldMorphism k)) :=
  Points.map (originToFibre k i) (originClosedPoint k)

/-- The second projection of the fibre sends `0ᵢ` to the `i`-th doubled origin. -/
theorem originPoint_snd (i : Fin 2) :
    Points.map (pullback.snd (originToY k) (foldMorphism k)) (originPoint k i) =
      ofOver.pointsEquiv (doubledOver k) (DoubledOrigin.origin k 1 i) :=
  sorry

/-- The subset `{0ᵢ | i ∈ s}` of the fibre over `0` is open. -/
theorem originFibreOpen_isOpen (s : Set (Fin 2)) :
    IsOpen (originPoint k '' s : Set (Points (pullback (originToY k) (foldMorphism k)))) :=
  sorry

/-- The open of `|Spec k ×_Y X|` on the origins indexed by `s`. -/
def originFibreOpen (s : Set (Fin 2)) :
    Opens (Points (pullback (originToY k) (foldMorphism k))) where
  carrier := originPoint k '' s
  is_open' := originFibreOpen_isOpen k s

/-- The restricted projection of `originFibreOpen s` to `Spec k` is finite. -/
theorem pointOfSubset_isFinite (s : Set (Fin 2)) :
    IsFinite
      ((OpenSubspace.ofOpens (originFibreOpen k s)).ι ≫
        pullback.fst (originToY k) (foldMorphism k)) :=
  sorry

/-- The finite-part point over `0` classified by a subset of `{0₁, 0₂}`. -/
def pointOfSubset (s : Set (Fin 2)) :
    Point (foldMorphism k) (originOver k) :=
  Point.of (originToY k) (originFibreOpen k s) (pointOfSubset_isFinite k s)

/-- The morphism to `Y` of `pointOfSubset s` is the zero section. -/
theorem pointOfSubset_a (s : Set (Fin 2)) :
    (pointOfSubset k s).a = originToY k :=
  sorry

/-- The open of `pointOfSubset s` is the origin subset indexed by `s`. -/
theorem pointOfSubset_Z (s : Set (Fin 2)) :
    (pointOfSubset k s).Z = originFibreOpen k s :=
  sorry

/-- Distinct subsets of `{0₁, 0₂}` determine distinct finite-part points over `0`. -/
theorem pointOfSubset_injective : Function.Injective (pointOfSubset k) :=
  sorry

/-- The subset of origins contained in a finite-part point over the zero section. -/
def subsetOfPointOverOrigin (p : Point (foldMorphism k) (originOver k))
    (hp : p.a = originToY k) : Set (Fin 2) :=
  {i | Points.map (pullback.congrHom hp rfl).inv (originPoint k i) ∈ p.Z}

/-- The identity triangle on `Y` used to identify `Y ×_Y X` with `X`. -/
theorem foldMorphism_id_w :
    foldMorphism k ≫ 𝟙 (ofOver (affineLineOver k)) =
      𝟙 (ofOver (doubledOver k)) ≫ foldMorphism k :=
  sorry

/-- The comparison `Y ×_Y X ≅ X` along the identity of `Y`. -/
def pullbackIdFoldIso :
    pullback (𝟙 (ofOver (affineLineOver k))) (foldMorphism k) ≅
      ofOver (doubledOver k) where
  hom := pullback.snd (𝟙 (ofOver (affineLineOver k))) (foldMorphism k)
  inv :=
    pullback.lift (foldMorphism k) (𝟙 (ofOver (doubledOver k)))
      (foldMorphism_id_w k)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The `i`-th doubled-origin chart, as an open of `|Y ×_Y X|`. -/
theorem chartFibreOpen_isOpen (i : Fin 2) :
    IsOpen
      (Points.map (pullbackIdFoldIso k).inv ''
        (ofOver.pointsEquiv (doubledOver k) ''
          (DoubledOrigin.chart k 1 i : Set (DoubledOrigin.scheme k 1)))) :=
  sorry

/-- The open of `|Y ×_Y X|` corresponding to the `i`-th affine chart of `X`. -/
def chartFibreOpen (i : Fin 2) :
    Opens
      (Points (pullback (𝟙 (ofOver (affineLineOver k))) (foldMorphism k))) where
  carrier :=
    Points.map (pullbackIdFoldIso k).inv ''
      (ofOver.pointsEquiv (doubledOver k) ''
        (DoubledOrigin.chart k 1 i : Set (DoubledOrigin.scheme k 1)))
  is_open' := chartFibreOpen_isOpen k i

/-- The empty open of `|Y ×_Y X|` is finite over `Y`. -/
theorem emptyLift_isFinite :
    IsFinite
      ((OpenSubspace.ofOpens
          (⊥ : Opens
            (Points
              (pullback (𝟙 (ofOver (affineLineOver k))) (foldMorphism k))))).ι ≫
        pullback.fst (𝟙 (ofOver (affineLineOver k))) (foldMorphism k)) :=
  sorry

/-- The finite-part pair over `Y` with empty open, lifting `∅`. -/
def emptyLift : Point (foldMorphism k) (affineLineOver k) :=
  Point.of (𝟙 (ofOver (affineLineOver k))) ⊥ (emptyLift_isFinite k)

/-- The morphism to `Y` of `emptyLift` is the identity of `Y`. -/
theorem emptyLift_a : (emptyLift k).a = 𝟙 (ofOver (affineLineOver k)) :=
  sorry

/-- The `i`-th chart open of `|Y ×_Y X|` is finite over `Y`. -/
theorem chartLift_isFinite (i : Fin 2) :
    IsFinite
      ((OpenSubspace.ofOpens (chartFibreOpen k i)).ι ≫
        pullback.fst (𝟙 (ofOver (affineLineOver k))) (foldMorphism k)) :=
  sorry

/-- The finite-part pair over `Y` cut out by the `i`-th chart, lifting `{0ᵢ}`. -/
def chartLift (i : Fin 2) : Point (foldMorphism k) (affineLineOver k) :=
  Point.of (𝟙 (ofOver (affineLineOver k))) (chartFibreOpen k i)
    (chartLift_isFinite k i)

/-- The morphism to `Y` of `chartLift i` is the identity of `Y`. -/
theorem chartLift_a (i : Fin 2) :
    (chartLift k i).a = 𝟙 (ofOver (affineLineOver k)) :=
  sorry

/-- A finite-part pair over `T` is étale-liftable if it is the restriction of a pair
`(a, Z)` along some morphism `T ⟶ U` with `a : U ⟶ Y` étale. -/
def IsEtaleLiftable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {T : Over S} (p : Point f T) : Prop :=
  ∃ (U : Over S) (h : T ⟶ U) (q : Point f U),
    Etale q.a ∧ q.restrict h = p

/-- Restricting the empty lift along the zero section recovers the empty origin point. -/
theorem emptyLift_restrict :
    (emptyLift k).restrict (zeroSectionOver k) = pointOfSubset k ∅ :=
  sorry

/-- Restricting the `i`-th chart lift along the zero section recovers `{0ᵢ}`. -/
theorem chartLift_restrict (i : Fin 2) :
    (chartLift k i).restrict (zeroSectionOver k) = pointOfSubset k {i} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
