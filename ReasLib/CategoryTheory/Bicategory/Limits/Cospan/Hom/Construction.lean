/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Basic

/-!
# Constructors for bicategorical cospan transformations

This leaf owns the explicit finite walking-cospan assembly behind `CospanTransform.mk`. Its
inputs are exactly the three vertex maps and the two generating comparison isomorphisms. The
reduction, identity, composition, and reconstruction API is intentionally kept in
`Hom.Computations`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.CospanTransform

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' x'' y'' z'' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}
variable {f'' : x'' ⟶ z''} {g'' : y'' ⟶ z''}

namespace Implementation

/- Implementation boundary: the finite walking-cospan case split is confined here. Public
users consume the five generator-level inputs to `mk` and its projection API. -/

/-- The three vertex components used to construct a strong transformation of cospans. -/
private def app (left : x ⟶ x') (right : y ⟶ y') (base : z ⟶ z') :
    ∀ a : LocallyDiscrete Limits.WalkingCospan,
      (cospan f g).obj a ⟶ (cospan f' g').obj a
  | ⟨none⟩ => base
  | ⟨some Limits.WalkingPair.left⟩ => left
  | ⟨some Limits.WalkingPair.right⟩ => right

/-- Naturality data on the identities and two generators before passage to the locally
discrete bicategory. -/
private def naturalityOfHom
    (left : x ⟶ x') (right : y ⟶ y') (base : z ⟶ z')
    (leftIso : left ≫ f' ≅ f ≫ base) (rightIso : right ≫ g' ≅ g ≫ base) :
    ∀ {a b : Limits.WalkingCospan} (h : a ⟶ b),
      (cospan f g).map (Quiver.Hom.toLoc h) ≫
          app left right base (LocallyDiscrete.mk b) ≅
        app left right base (LocallyDiscrete.mk a) ≫
          (cospan f' g').map (Quiver.Hom.toLoc h)
  | _, _, .id _ => λ_ _ ≪≫ (ρ_ _).symm
  | _, _, .term Limits.WalkingPair.left => leftIso.symm
  | _, _, .term Limits.WalkingPair.right => rightIso.symm

/-- Naturality data on the canonical locally discrete walking-cospan pseudofunctors. -/
private def naturality
    (left : x ⟶ x') (right : y ⟶ y') (base : z ⟶ z')
    (leftIso : left ≫ f' ≅ f ≫ base) (rightIso : right ≫ g' ≅ g ≫ base)
    {a b : LocallyDiscrete Limits.WalkingCospan} (h : a ⟶ b) :
    (cospan f g).map h ≫ app left right base b ≅
      app left right base a ≫ (cospan f' g').map h :=
  naturalityOfHom left right base leftIso rightIso h.as

/-- The generator-wise naturality data respect `2`-morphisms of the locally discrete walking
cospan. -/
private theorem naturality_naturality
    (left : x ⟶ x') (right : y ⟶ y') (base : z ⟶ z')
    (leftIso : left ≫ f' ≅ f ≫ base) (rightIso : right ≫ g' ≅ g ≫ base) :
    ∀ {a b : LocallyDiscrete Limits.WalkingCospan} {h k : a ⟶ b} (η : h ⟶ k),
      (cospan f g).map₂ η ▷ app left right base b ≫
          (naturality left right base leftIso rightIso k).hom =
        (naturality left right base leftIso rightIso h).hom ≫
          app left right base a ◁ (cospan f' g').map₂ η := sorry

/-- The generator-wise naturality data satisfy strong-transformation identity coherence. -/
private theorem naturality_id
    (left : x ⟶ x') (right : y ⟶ y') (base : z ⟶ z')
    (leftIso : left ≫ f' ≅ f ≫ base) (rightIso : right ≫ g' ≅ g ≫ base) :
    ∀ a : LocallyDiscrete Limits.WalkingCospan,
      (naturality left right base leftIso rightIso (𝟙 a)).hom ≫
          app left right base a ◁ ((cospan f' g').mapId a).hom =
        ((cospan f g).mapId a).hom ▷ app left right base a ≫
          (λ_ (app left right base a)).hom ≫
            (ρ_ (app left right base a)).inv := sorry

/-- The generator-wise naturality data satisfy strong-transformation composition coherence. -/
private theorem naturality_comp
    (left : x ⟶ x') (right : y ⟶ y') (base : z ⟶ z')
    (leftIso : left ≫ f' ≅ f ≫ base) (rightIso : right ≫ g' ≅ g ≫ base) :
    ∀ {a b c : LocallyDiscrete Limits.WalkingCospan} (h : a ⟶ b) (k : b ⟶ c),
      (naturality left right base leftIso rightIso (h ≫ k)).hom ≫
          app left right base a ◁ ((cospan f' g').mapComp h k).hom =
        ((cospan f g).mapComp h k).hom ▷ app left right base c ≫
          (α_ _ _ _).hom ≫
            (cospan f g).map h ◁
              (naturality left right base leftIso rightIso k).hom ≫
            (α_ _ _ _).inv ≫
              (naturality left right base leftIso rightIso h).hom ▷
                (cospan f' g').map k ≫
              (α_ _ _ _).hom := sorry

end Implementation

/-- Construct a strong transformation of walking-cospan diagrams from its three vertex maps and
the two generating comparison isomorphisms. All non-`Prop` transformation data are explicit. -/
@[stacks 0040 "constructor for a bicategorical cospan transformation"]
def mk
    (left : x ⟶ x') (right : y ⟶ y') (base : z ⟶ z')
    (leftIso : left ≫ f' ≅ f ≫ base) (rightIso : right ≫ g' ≅ g ≫ base) :
    CospanTransform f g f' g' where
  app := Implementation.app left right base
  naturality := Implementation.naturality left right base leftIso rightIso
  naturality_naturality :=
    Implementation.naturality_naturality left right base leftIso rightIso
  naturality_id := Implementation.naturality_id left right base leftIso rightIso
  naturality_comp := Implementation.naturality_comp left right base leftIso rightIso

/- Data audit (mathlib 4.32): `mk` stores the three supplied vertex maps and two supplied
comparison isomorphisms explicitly. Deferred content is confined to the strong-transformation
coherence fields; no component or comparison cell is selected by a placeholder. -/

end CategoryTheory.Bicategory.CospanTransform
