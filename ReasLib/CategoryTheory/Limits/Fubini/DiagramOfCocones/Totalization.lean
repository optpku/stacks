/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Fubini
public import Mathlib.CategoryTheory.Limits.ConeCategory

/-!
# Cocone totalization for Fubini diagrams

This module owns the functors that totalize cocones on row cocone points and,
under chosen row colimits, recover row cocone points from a cocone on the
uncurried diagram. The resulting equivalence is kept in the companion
`Equivalence` module.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Limits

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory Functor

variable {I : Type u₁} [Category.{v₁} I]
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u₃} [Category.{v₃} C]

namespace DiagramOfCocones

variable {F : I ⥤ J ⥤ C} (D : DiagramOfCocones F)

section

namespace Implementation

/-- Naturality of the legs of the total cocone assembled from a row cocone and an outer
cocone. -/
private theorem totalCocone_naturality (c : Cocone D.coconePoints)
    {p q : I × J} (f : p ⟶ q) :
    (uncurry.obj F).map f ≫ ((D.obj q.1).ι.app q.2 ≫ c.ι.app q.1) =
      ((D.obj p.1).ι.app p.2 ≫ c.ι.app p.1) ≫
        ((const (I × J)).obj c.pt).map f := sorry
/- Proof strategy: decompose `f` into its product components and combine row cocone
naturality, compatibility of `D.map`, and outer cocone naturality. -/

/-- Totalize an outer cocone on the row vertices to a cocone on the uncurried diagram.

Its leg at `(i, j)` is the row leg at `j` followed by the outer leg at `i`. This is the
object-level owner used by `totalCoconeFunctor`. -/
def _root_.CategoryTheory.Limits.DiagramOfCocones.totalCocone
    (c : Cocone D.coconePoints) : Cocone (uncurry.obj F) where
  pt := c.pt
  ι :=
    { app := fun p => (D.obj p.1).ι.app p.2 ≫ c.ι.app p.1
      naturality := fun _ _ f => totalCocone_naturality D c f }

/-- Compatibility of the unchanged vertex map with total cocone legs. -/
private theorem totalCoconeMap_w {c₁ c₂ : Cocone D.coconePoints}
    (α : c₁ ⟶ c₂) (p : I × J) :
    (totalCocone D c₁).ι.app p ≫ α.hom = (totalCocone D c₂).ι.app p := sorry
/- Proof strategy: reassociate the row leg and apply the cocone-morphism equation `α.w` at
`p.1`. -/

/-- The morphism map underlying cocone totalization. -/
private def totalCoconeMap {c₁ c₂ : Cocone D.coconePoints} (α : c₁ ⟶ c₂) :
    totalCocone D c₁ ⟶ totalCocone D c₂ where
  hom := α.hom
  w := totalCoconeMap_w D α

/-- Total cocone maps preserve identities. -/
private theorem totalCoconeMap_id (c : Cocone D.coconePoints) :
    totalCoconeMap D (𝟙 c) = 𝟙 (totalCocone D c) := sorry
/- Proof strategy: apply cocone-morphism extensionality; both vertex maps are identities. -/

/-- Total cocone maps preserve composition. -/
private theorem totalCoconeMap_comp {c₁ c₂ c₃ : Cocone D.coconePoints}
    (α : c₁ ⟶ c₂) (β : c₂ ⟶ c₃) :
    totalCoconeMap D (α ≫ β) = totalCoconeMap D α ≫ totalCoconeMap D β := sorry
/- Proof strategy: apply cocone-morphism extensionality; both vertex maps are
`α.hom ≫ β.hom`. -/

end Implementation

/-- Totalization sends an outer cocone on the row vertices to the cocone on the uncurried
diagram whose legs are the row legs followed by the outer legs. -/
def totalCoconeFunctor : Cocone D.coconePoints ⥤ Cocone (uncurry.obj F) where
  obj := D.totalCocone
  map := Implementation.totalCoconeMap D
  map_id := Implementation.totalCoconeMap_id D
  map_comp := Implementation.totalCoconeMap_comp D

/-- Totalization preserves the vertex of an outer cocone. -/
@[simp]
lemma totalCocone_pt (c : Cocone D.coconePoints) :
    (D.totalCocone c).pt = c.pt := sorry
/- Proof strategy: unfold `totalCocone`; its vertex is definitionally the outer vertex. -/

/-- A leg of a total cocone is the row leg followed by the corresponding outer leg. -/
@[simp, reassoc]
lemma totalCocone_ι_app (c : Cocone D.coconePoints) (p : I × J) :
    (D.totalCocone c).ι.app p = (D.obj p.1).ι.app p.2 ≫ c.ι.app p.1 := sorry
/- Proof strategy: unfold `totalCocone`; this is its defining component formula. -/

/-- Totalization preserves the vertex of an outer cocone. -/
@[simp]
lemma totalCoconeFunctor_obj_pt (c : Cocone D.coconePoints) :
    (D.totalCoconeFunctor.obj c).pt = c.pt := sorry
/- Proof strategy: unfold `totalCoconeFunctor` and `DiagramOfCocones.totalCocone`; the
object constructor keeps the outer cocone vertex unchanged. -/

/-- A leg of the totalized cocone is a row leg followed by the corresponding outer leg. -/
@[simp, reassoc]
lemma totalCoconeFunctor_obj_ι_app (c : Cocone D.coconePoints) (p : I × J) :
    (D.totalCoconeFunctor.obj c).ι.app p =
      (D.obj p.1).ι.app p.2 ≫ c.ι.app p.1 := sorry
/- Proof strategy: unfold the public functor and `D.totalCocone`; the component at
`p` is the displayed composite. -/

/-- Totalization is the identity on the vertex morphism of a cocone morphism. -/
@[simp]
lemma totalCoconeFunctor_map_hom {c₁ c₂ : Cocone D.coconePoints} (α : c₁ ⟶ c₂) :
    (D.totalCoconeFunctor.map α).hom = α.hom := sorry
/- Proof strategy: unfold the public functor and `Implementation.totalCoconeMap`. -/

namespace Implementation

/-- Compatibility of the unchanged vertex map with the canonical row-point cocones. -/
private theorem coconePointsMap_w (hD : ∀ i, IsColimit (D.obj i))
    {c₁ c₂ : Cocone (uncurry.obj F)} (α : c₁ ⟶ c₂) (i : I) :
    (coconeOfCoconeUncurry hD c₁).ι.app i ≫ α.hom =
      (coconeOfCoconeUncurry hD c₂).ι.app i := sorry
/- Proof strategy: use `IsColimit.hom_ext (hD i)`; after precomposition with row legs the
claim is `α.w`. -/

/-- The morphism map underlying the row-point inverse functor. -/
private def coconePointsMap (hD : ∀ i, IsColimit (D.obj i))
    {c₁ c₂ : Cocone (uncurry.obj F)} (α : c₁ ⟶ c₂) :
    coconeOfCoconeUncurry hD c₁ ⟶ coconeOfCoconeUncurry hD c₂ where
  hom := α.hom
  w := coconePointsMap_w D hD α

/-- Row-point cocone maps preserve identities. -/
private theorem coconePointsMap_id (hD : ∀ i, IsColimit (D.obj i))
    (c : Cocone (uncurry.obj F)) :
    coconePointsMap D hD (𝟙 c) = 𝟙 _ := sorry
/- Proof strategy: apply cocone-morphism extensionality to the unchanged identity vertex map. -/

/-- Row-point cocone maps preserve composition. -/
private theorem coconePointsMap_comp (hD : ∀ i, IsColimit (D.obj i))
    {c₁ c₂ c₃ : Cocone (uncurry.obj F)} (α : c₁ ⟶ c₂) (β : c₂ ⟶ c₃) :
    coconePointsMap D hD (α ≫ β) =
      coconePointsMap D hD α ≫ coconePointsMap D hD β := sorry
/- Proof strategy: apply cocone-morphism extensionality to the unchanged composite vertex map. -/

end Implementation

/-- If the row cocones of `D` are colimiting, a cocone on the uncurried diagram restricts
functorially to a cocone on their vertices. -/
def coconePointsFunctor (hD : ∀ i, IsColimit (D.obj i)) :
    Cocone (uncurry.obj F) ⥤ Cocone D.coconePoints where
  obj := coconeOfCoconeUncurry hD
  map := Implementation.coconePointsMap D hD
  map_id := Implementation.coconePointsMap_id D hD
  map_comp := Implementation.coconePointsMap_comp D hD

/-- The row-point functor uses the canonical cocone induced from a total cocone. -/
@[simp]
lemma coconePointsFunctor_obj (hD : ∀ i, IsColimit (D.obj i))
    (c : Cocone (uncurry.obj F)) :
    (D.coconePointsFunctor hD).obj c = coconeOfCoconeUncurry hD c := sorry
/- Proof strategy: unfold `coconePointsFunctor`; its object field is the canonical mathlib
construction `coconeOfCoconeUncurry hD`. -/

/-- The row-point functor is the identity on vertex morphisms. -/
@[simp]
lemma coconePointsFunctor_map_hom (hD : ∀ i, IsColimit (D.obj i))
    {c₁ c₂ : Cocone (uncurry.obj F)} (α : c₁ ⟶ c₂) :
    ((D.coconePointsFunctor hD).map α).hom = α.hom := sorry
/- Proof strategy: unfold the public functor and `Implementation.coconePointsMap`. -/

end

end DiagramOfCocones

end CategoryTheory.Limits
