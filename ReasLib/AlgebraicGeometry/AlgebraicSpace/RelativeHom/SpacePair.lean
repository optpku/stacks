module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Basic

/-!
# Relative Hom pairs over an algebraic space

Pairs of a base morphism and a relative morphism are defined over arbitrary
algebraic-space test objects.
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
private theorem pullback_lift_condition {T T' : AlgebraicSpace S} (h : T' ⟶ T)
    (p : SpacePair Z X T) :
    pullback.fst (h ≫ p.base) Z.hom ≫ (h ≫ p.base) =
      (fiberMap h p ≫ p.hom.left ≫ pullback.snd p.base X.hom) ≫ X.hom :=
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
        (by exact pullback_lift_condition h p))
      (pullback.lift_fst _ _ _)

/-- View a pair as a morphism `T ×_{a, B} Z ⟶ X`. -/
def toOverMorph {T : AlgebraicSpace S} (p : SpacePair Z X T) :
    pullback p.base Z.hom ⟶ X.left :=
  p.hom.left ≫ pullback.snd p.base X.hom

/-- The morphism `toOverMorph p` makes the triangle over `B` commute. -/
theorem toOverMorph_over_base {T : AlgebraicSpace S} (p : SpacePair Z X T) :
    toOverMorph p ≫ X.hom = pullback.fst p.base Z.hom ≫ p.base :=
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
        w.symm)
      (pullback.lift_fst _ _ _)

/-- Pairs over a represented scheme are equivalent to scheme-test relative morphisms. -/
def schemeEquiv (Z X : Over B) (T : Over S) :
    SpacePair Z X (ofOver T) ≃ Pair Z.hom X.hom T where
  toFun p := ⟨p.base, p.hom⟩
  invFun p := ⟨p.a, p.b⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- The scheme comparison preserves the base morphism. -/
theorem schemeEquiv_a (Z X : Over B) {T : Over S} (p : SpacePair Z X (ofOver T)) :
    (schemeEquiv Z X T p).a = p.base := rfl

/-- The scheme comparison preserves the morphism over the test scheme. -/
theorem schemeEquiv_b (Z X : Over B) {T : Over S} (p : SpacePair Z X (ofOver T)) :
    (schemeEquiv Z X T p).b = p.hom := rfl

end SpacePair

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
