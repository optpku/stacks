module

public import stacks_project.Chap97.«97_10_0_2_Morphism»

/-!
# Relative Hom pairs over an algebraic space

The 05Y1 pairs `(a, b)` for `Mor_B(Z, X)`, with the test object an algebraic
space over `S` rather than a scheme over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

/-- A pair `(a, b)` consisting of a morphism `a : T ⟶ B` of algebraic spaces over
`S` and a morphism `b` over `T` from `T ×_{a, B} Z` to `T ×_{a, B} X`. -/
structure SpacePair {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    (T : AlgebraicSpace S) : Type (u + 1) where
  /-- The test morphism `a : T ⟶ B`. -/
  base : T ⟶ B
  /-- The morphism over `T` between the fibre products with `Z` and `X`. -/
  hom : Over.mk (pullback.fst base Z.hom) ⟶ Over.mk (pullback.fst base X.hom)

namespace SpacePair

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}

/-- Build a pair from a test morphism `a : T ⟶ B` and a morphism over `T`. -/
def of {T : AlgebraicSpace S} (base : T ⟶ B)
    (hom : Over.mk (pullback.fst base Z.hom) ⟶ Over.mk (pullback.fst base X.hom)) :
    SpacePair Z X T where
  base := base
  hom := hom

/-- The underlying arrow of `p.hom` commutes with the projections to `T`. -/
theorem spec {T : AlgebraicSpace S} (p : SpacePair Z X T) :
    p.hom.left ≫ pullback.fst p.base X.hom = pullback.fst p.base Z.hom :=
  sorry

/-- The comparison `T' ×_{a ∘ h, B} Z ⟶ T ×_{a, B} Z` induced by `h : T' ⟶ T`. -/
def fiberMap {T T' : AlgebraicSpace S} (h : T' ⟶ T) (p : SpacePair Z X T) :
    pullback (h ≫ p.base) Z.hom ⟶ pullback p.base Z.hom :=
  pullback.map (h ≫ p.base) Z.hom p.base Z.hom h (𝟙 Z.left) (𝟙 B)
    (Category.comp_id (h ≫ p.base))
    ((Category.comp_id Z.hom).trans (Category.id_comp Z.hom).symm)

/-- The maps `pr₀` and `fiberMap h p ≫ p.hom.left ≫ pr₁` agree over `B`. -/
theorem pullback_lift_condition {T T' : AlgebraicSpace S} (h : T' ⟶ T)
    (p : SpacePair Z X T) :
    pullback.fst (h ≫ p.base) Z.hom ≫ (h ≫ p.base) =
      (fiberMap h p ≫ p.hom.left ≫ pullback.snd p.base X.hom) ≫ X.hom :=
  sorry

/-- The mediating morphism of `SpacePair.map h p` projects to `T'` as
`pullback.fst (h ≫ p.base) Z.hom`. -/
theorem pullback_fst {T T' : AlgebraicSpace S} (h : T' ⟶ T) (p : SpacePair Z X T) :
    pullback.lift (pullback.fst (h ≫ p.base) Z.hom)
        (fiberMap h p ≫ p.hom.left ≫ pullback.snd p.base X.hom)
        (pullback_lift_condition h p) ≫
      pullback.fst (h ≫ p.base) X.hom =
      pullback.fst (h ≫ p.base) Z.hom :=
  sorry

/-- Restriction of a pair `(a, b)` along `h : T' ⟶ T`, sending `a` to `h ≫ a`
and `b` to the induced morphism over `T'`. -/
def map {T T' : AlgebraicSpace S} (h : T' ⟶ T) (p : SpacePair Z X T) :
    SpacePair Z X T' where
  base := h ≫ p.base
  hom :=
    Over.homMk
      (pullback.lift (pullback.fst (h ≫ p.base) Z.hom)
        (fiberMap h p ≫ p.hom.left ≫ pullback.snd p.base X.hom)
        (pullback_lift_condition h p))
      (pullback_fst h p)

/-- View a pair as a morphism `T ×_{a, B} Z ⟶ X`. -/
def toOverMorph {T : AlgebraicSpace S} (p : SpacePair Z X T) :
    pullback p.base Z.hom ⟶ X.left :=
  p.hom.left ≫ pullback.snd p.base X.hom

/-- The morphism `toOverMorph p` makes the triangle over `B` commute. -/
theorem toOverMorph_over_base {T : AlgebraicSpace S} (p : SpacePair Z X T) :
    toOverMorph p ≫ X.hom = pullback.fst p.base Z.hom ≫ p.base :=
  sorry

/-- The lift condition for `ofOverMorph`, swapping the over-`B` triangle. -/
theorem ofOverMorph_lift_condition {T : AlgebraicSpace S} (a : T ⟶ B)
    (b : pullback a Z.hom ⟶ X.left)
    (w : b ≫ X.hom = pullback.fst a Z.hom ≫ a) :
    pullback.fst a Z.hom ≫ a = b ≫ X.hom :=
  sorry

/-- The mediating morphism of `ofOverMorph` projects to `T` as
`pullback.fst a Z.hom`. -/
theorem ofOverMorph_fst {T : AlgebraicSpace S} (a : T ⟶ B)
    (b : pullback a Z.hom ⟶ X.left)
    (w : b ≫ X.hom = pullback.fst a Z.hom ≫ a) :
    pullback.lift (pullback.fst a Z.hom) b (ofOverMorph_lift_condition a b w) ≫
      pullback.fst a X.hom =
      pullback.fst a Z.hom :=
  sorry

/-- Reconstruct a pair from a test morphism `a` and a morphism
`b : T ×_{a, B} Z ⟶ X` making the triangle over `B` commute. -/
def ofOverMorph {T : AlgebraicSpace S} (a : T ⟶ B)
    (b : pullback a Z.hom ⟶ X.left)
    (w : b ≫ X.hom = pullback.fst a Z.hom ≫ a) :
    SpacePair Z X T where
  base := a
  hom :=
    Over.homMk (pullback.lift (pullback.fst a Z.hom) b
        (ofOverMorph_lift_condition a b w))
      (ofOverMorph_fst a b w)

end SpacePair

/-- Pairs over the algebraic space `ofOver T` correspond to scheme-level `HomPair`
values of `Mor_B(Z, X)`. -/
def overEquiv {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) (T : Over S) :
    SpacePair Z X (ofOver T) ≃ HomPair Z X T where
  toFun p := ⟨p.base, p.hom⟩
  invFun p := ⟨p.base, p.hom⟩
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `overEquiv` keeps the test morphism `a`. -/
theorem overEquiv_base {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    {T : Over S} (p : SpacePair Z X (ofOver T)) :
    (overEquiv Z X T p).base = p.base :=
  sorry

/-- The forward map of `overEquiv` keeps the over-`T` morphism `b`. -/
theorem overEquiv_hom {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    {T : Over S} (p : SpacePair Z X (ofOver T)) :
    (overEquiv Z X T p).hom = p.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
