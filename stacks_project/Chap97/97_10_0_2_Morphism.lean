/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Relative morphism pairs of algebraic spaces

A test morphism `a : ofOver T ⟶ B` determines fibre products
`pullback a Z.hom` and `pullback a X.hom`. A pair `(a, b)` packages this
test morphism with a morphism over `ofOver T` between those fibre products.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

/-- A pair `(a, b)` consisting of a test morphism `a : ofOver T ⟶ B` and a
morphism `b` over `ofOver T` from `pullback a Z.hom` to `pullback a X.hom`. -/
structure HomPair {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    (T : Over S) : Type (u + 1) where
  /-- The test morphism `a : ofOver T ⟶ B`. -/
  base : ofOver T ⟶ B
  /-- The morphism over `ofOver T` between the fibre products with `Z` and `X`. -/
  hom : Over.mk (pullback.fst base Z.hom) ⟶ Over.mk (pullback.fst base X.hom)

namespace HomPair

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}

/-- The comparison `T' ×_{a ∘ f, B} Z ⟶ T ×_{a, B} Z` induced by `f : T' ⟶ T`. -/
def fiberMap {T T' : Over S} (f : T' ⟶ T) (p : HomPair Z X T) :
    Limits.pullback (ofOverMap f ≫ p.base) Z.hom ⟶
      Limits.pullback p.base Z.hom :=
  Limits.pullback.map (ofOverMap f ≫ p.base) Z.hom p.base Z.hom
    (ofOverMap f) (𝟙 Z.left) (𝟙 B)
    (Category.comp_id (ofOverMap f ≫ p.base))
    ((Category.comp_id Z.hom).trans (Category.id_comp Z.hom).symm)

/-- The maps `pr₀` and `fiberMap f p ≫ p.hom.left ≫ pr₁` agree over `B`. -/
theorem pullback_lift_condition {T T' : Over S} (f : T' ⟶ T) (p : HomPair Z X T) :
    Limits.pullback.fst (ofOverMap f ≫ p.base) Z.hom ≫ (ofOverMap f ≫ p.base) =
      (fiberMap f p ≫ p.hom.left ≫ Limits.pullback.snd p.base X.hom) ≫ X.hom :=
  sorry

/-- The mediating morphism of `HomPair.pullback f p` projects to `ofOver T'` as
`Limits.pullback.fst (ofOverMap f ≫ p.base) Z.hom`. -/
theorem pullback_fst {T T' : Over S} (f : T' ⟶ T) (p : HomPair Z X T) :
    Limits.pullback.lift (Limits.pullback.fst (ofOverMap f ≫ p.base) Z.hom)
        (fiberMap f p ≫ p.hom.left ≫ Limits.pullback.snd p.base X.hom)
        (pullback_lift_condition f p) ≫
      Limits.pullback.fst (ofOverMap f ≫ p.base) X.hom =
      Limits.pullback.fst (ofOverMap f ≫ p.base) Z.hom :=
  sorry

/-- Restriction of a pair `(a, b)` along `f : T' ⟶ T`, sending `a` to
`ofOverMap f ≫ a` and `b` to the induced morphism over `ofOver T'`. -/
def pullback {T T' : Over S} (f : T' ⟶ T) (p : HomPair Z X T) :
    HomPair Z X T' where
  base := ofOverMap f ≫ p.base
  hom :=
    Over.homMk
      (Limits.pullback.lift (Limits.pullback.fst (ofOverMap f ≫ p.base) Z.hom)
        (fiberMap f p ≫ p.hom.left ≫ Limits.pullback.snd p.base X.hom)
        (pullback_lift_condition f p))
      (pullback_fst f p)

/-- The underlying arrow of `p.hom` commutes with the projections to `ofOver T`. -/
theorem spec {T : Over S} (p : HomPair Z X T) :
    p.hom.left ≫ Limits.pullback.fst p.base X.hom =
      Limits.pullback.fst p.base Z.hom :=
  sorry

/-- View a pair as a morphism `T ×_{a, B} Z ⟶ X`. -/
def toOverMorph {T : Over S} (p : HomPair Z X T) :
    Limits.pullback p.base Z.hom ⟶ X.left :=
  p.hom.left ≫ Limits.pullback.snd p.base X.hom

/-- The morphism `toOverMorph p` makes the triangle over `B` commute. -/
theorem toOverMorph_over_base {T : Over S} (p : HomPair Z X T) :
    toOverMorph p ≫ X.hom = Limits.pullback.fst p.base Z.hom ≫ p.base :=
  sorry

/-- The lift condition for `ofOverMorph`, swapping the over-`B` triangle. -/
theorem ofOverMorph_lift_condition {T : Over S} (a : ofOver T ⟶ B)
    (b : Limits.pullback a Z.hom ⟶ X.left)
    (w : b ≫ X.hom = Limits.pullback.fst a Z.hom ≫ a) :
    Limits.pullback.fst a Z.hom ≫ a = b ≫ X.hom :=
  sorry

/-- The mediating morphism of `ofOverMorph` projects to `ofOver T` as
`Limits.pullback.fst a Z.hom`. -/
theorem ofOverMorph_fst {T : Over S} (a : ofOver T ⟶ B)
    (b : Limits.pullback a Z.hom ⟶ X.left)
    (w : b ≫ X.hom = Limits.pullback.fst a Z.hom ≫ a) :
    Limits.pullback.lift (Limits.pullback.fst a Z.hom) b
        (ofOverMorph_lift_condition a b w) ≫
      Limits.pullback.fst a X.hom =
      Limits.pullback.fst a Z.hom :=
  sorry

/-- Reconstruct a pair from a test morphism `a` and a morphism
`b : T ×_{a, B} Z ⟶ X` making the triangle over `B` commute. -/
def ofOverMorph {T : Over S} (a : ofOver T ⟶ B)
    (b : Limits.pullback a Z.hom ⟶ X.left)
    (w : b ≫ X.hom = Limits.pullback.fst a Z.hom ≫ a) :
    HomPair Z X T where
  base := a
  hom :=
    Over.homMk
      (Limits.pullback.lift (Limits.pullback.fst a Z.hom) b
        (ofOverMorph_lift_condition a b w))
      (ofOverMorph_fst a b w)

end HomPair

/-- Pairs over `T` are equivalent to morphisms `T ×_{a, B} Z ⟶ X` over `B`. -/
noncomputable def homPairEquiv {S : Scheme.{u}} {B : AlgebraicSpace S}
    (Z X : Over B) (T : Over S) :
    HomPair Z X T ≃
      Σ' (a : ofOver T ⟶ B) (b : pullback a Z.hom ⟶ X.left),
        b ≫ X.hom = pullback.fst a Z.hom ≫ a where
  toFun p := ⟨p.base, HomPair.toOverMorph p, HomPair.toOverMorph_over_base p⟩
  invFun q := HomPair.ofOverMorph q.1 q.2.1 q.2.2
  left_inv := sorry
  right_inv := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
