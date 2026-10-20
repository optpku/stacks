/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Fubini
public import Mathlib.CategoryTheory.Limits.ConeCategory

/-!
# Cone totalization for Fubini diagrams

This module owns the functors that totalize cones on row cone points and,
under chosen row limits, recover row cone points from a cone on the uncurried
diagram. The resulting equivalence is kept in the companion `Equivalence`
module.
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

namespace DiagramOfCones

variable {F : I ⥤ J ⥤ C} (D : DiagramOfCones F)

section

namespace Implementation

/-- Naturality of the legs of the total cone assembled from an outer cone and row cones. -/
private theorem totalCone_naturality (c : Cone D.conePoints)
    {p q : I × J} (f : p ⟶ q) :
    ((const (I × J)).obj c.pt).map f ≫
        (c.π.app q.1 ≫ (D.obj q.1).π.app q.2) =
      (c.π.app p.1 ≫ (D.obj p.1).π.app p.2) ≫ (uncurry.obj F).map f := sorry
/- Proof strategy: decompose `f` into its product components and combine outer cone
naturality, compatibility of `D.map`, and row cone naturality. -/

/-- Totalize an outer cone on the row vertices to a cone on the uncurried diagram.

Its leg at `(i, j)` is the outer leg at `i` followed by the row leg at `j`. This is the
object-level owner used by `totalConeFunctor`. -/
def _root_.CategoryTheory.Limits.DiagramOfCones.totalCone
    (c : Cone D.conePoints) : Cone (uncurry.obj F) where
  pt := c.pt
  π :=
    { app := fun p => c.π.app p.1 ≫ (D.obj p.1).π.app p.2
      naturality := fun _ _ f => totalCone_naturality D c f }

/-- Compatibility of the unchanged vertex map with total cone legs. -/
private theorem totalConeMap_w {c₁ c₂ : Cone D.conePoints}
    (α : c₁ ⟶ c₂) (p : I × J) :
    α.hom ≫ (totalCone D c₂).π.app p = (totalCone D c₁).π.app p := sorry
/- Proof strategy: reassociate the outer leg and apply the cone-morphism equation `α.w` at
`p.1`. -/

/-- The morphism map underlying cone totalization. -/
private def totalConeMap {c₁ c₂ : Cone D.conePoints} (α : c₁ ⟶ c₂) :
    totalCone D c₁ ⟶ totalCone D c₂ where
  hom := α.hom
  w := totalConeMap_w D α

/-- Total cone maps preserve identities. -/
private theorem totalConeMap_id (c : Cone D.conePoints) :
    totalConeMap D (𝟙 c) = 𝟙 (totalCone D c) := sorry
/- Proof strategy: apply cone-morphism extensionality; both vertex maps are identities. -/

/-- Total cone maps preserve composition. -/
private theorem totalConeMap_comp {c₁ c₂ c₃ : Cone D.conePoints}
    (α : c₁ ⟶ c₂) (β : c₂ ⟶ c₃) :
    totalConeMap D (α ≫ β) = totalConeMap D α ≫ totalConeMap D β := sorry
/- Proof strategy: apply cone-morphism extensionality; both vertex maps are
`α.hom ≫ β.hom`. -/

end Implementation

/-- Totalization sends an outer cone on the row vertices to the cone on the uncurried diagram
whose legs are the outer legs followed by the row legs. -/
def totalConeFunctor : Cone D.conePoints ⥤ Cone (uncurry.obj F) where
  obj := D.totalCone
  map := Implementation.totalConeMap D
  map_id := Implementation.totalConeMap_id D
  map_comp := Implementation.totalConeMap_comp D

/-- Totalization preserves the vertex of an outer cone. -/
@[simp]
lemma totalCone_pt (c : Cone D.conePoints) :
    (D.totalCone c).pt = c.pt := sorry
/- Proof strategy: unfold `totalCone`; its vertex is definitionally the outer vertex. -/

/-- A leg of a total cone is the outer leg followed by the corresponding row leg. -/
@[simp, reassoc]
lemma totalCone_π_app (c : Cone D.conePoints) (p : I × J) :
    (D.totalCone c).π.app p = c.π.app p.1 ≫ (D.obj p.1).π.app p.2 := sorry
/- Proof strategy: unfold `totalCone`; this is its defining component formula. -/

/-- Totalization preserves the vertex of an outer cone. -/
@[simp]
lemma totalConeFunctor_obj_pt (c : Cone D.conePoints) :
    (D.totalConeFunctor.obj c).pt = c.pt := sorry
/- Proof strategy: unfold `totalConeFunctor` and `DiagramOfCones.totalCone`; the object
constructor keeps the outer cone vertex unchanged. -/

/-- A leg of the totalized cone is an outer leg followed by the corresponding row leg. -/
@[simp, reassoc]
lemma totalConeFunctor_obj_π_app (c : Cone D.conePoints) (p : I × J) :
    (D.totalConeFunctor.obj c).π.app p =
      c.π.app p.1 ≫ (D.obj p.1).π.app p.2 := sorry
/- Proof strategy: unfold the public functor and `D.totalCone`; the component at
`p` is the displayed composite. -/

/-- Totalization is the identity on the vertex morphism of a cone morphism. -/
@[simp]
lemma totalConeFunctor_map_hom {c₁ c₂ : Cone D.conePoints} (α : c₁ ⟶ c₂) :
    (D.totalConeFunctor.map α).hom = α.hom := sorry
/- Proof strategy: unfold the public functor and `Implementation.totalConeMap`. -/

namespace Implementation

/-- Compatibility of the unchanged vertex map with the canonical row-point cones. -/
private theorem conePointsMap_w (hD : ∀ i, IsLimit (D.obj i))
    {c₁ c₂ : Cone (uncurry.obj F)} (α : c₁ ⟶ c₂) (i : I) :
    α.hom ≫ (coneOfConeUncurry hD c₂).π.app i =
      (coneOfConeUncurry hD c₁).π.app i := sorry
/- Proof strategy: use `IsLimit.hom_ext (hD i)`; after postcomposition with row legs the claim
is `α.w`. -/

/-- The morphism map underlying the row-point inverse functor. -/
private def conePointsMap (hD : ∀ i, IsLimit (D.obj i))
    {c₁ c₂ : Cone (uncurry.obj F)} (α : c₁ ⟶ c₂) :
    coneOfConeUncurry hD c₁ ⟶ coneOfConeUncurry hD c₂ where
  hom := α.hom
  w := conePointsMap_w D hD α

/-- Row-point cone maps preserve identities. -/
private theorem conePointsMap_id (hD : ∀ i, IsLimit (D.obj i))
    (c : Cone (uncurry.obj F)) :
    conePointsMap D hD (𝟙 c) = 𝟙 _ := sorry
/- Proof strategy: apply cone-morphism extensionality to the unchanged identity vertex map. -/

/-- Row-point cone maps preserve composition. -/
private theorem conePointsMap_comp (hD : ∀ i, IsLimit (D.obj i))
    {c₁ c₂ c₃ : Cone (uncurry.obj F)} (α : c₁ ⟶ c₂) (β : c₂ ⟶ c₃) :
    conePointsMap D hD (α ≫ β) =
      conePointsMap D hD α ≫ conePointsMap D hD β := sorry
/- Proof strategy: apply cone-morphism extensionality to the unchanged composite vertex map. -/

end Implementation

/-- If the row cones of `D` are limiting, a cone on the uncurried diagram restricts
functorially to a cone on their vertices. -/
def conePointsFunctor (hD : ∀ i, IsLimit (D.obj i)) :
    Cone (uncurry.obj F) ⥤ Cone D.conePoints where
  obj := coneOfConeUncurry hD
  map := Implementation.conePointsMap D hD
  map_id := Implementation.conePointsMap_id D hD
  map_comp := Implementation.conePointsMap_comp D hD

/-- The row-point functor uses the canonical cone induced from a total cone. -/
@[simp]
lemma conePointsFunctor_obj (hD : ∀ i, IsLimit (D.obj i))
    (c : Cone (uncurry.obj F)) :
    (D.conePointsFunctor hD).obj c = coneOfConeUncurry hD c := sorry
/- Proof strategy: unfold `conePointsFunctor`; its object field is the canonical mathlib
construction `coneOfConeUncurry hD`. -/

/-- The row-point functor is the identity on vertex morphisms. -/
@[simp]
lemma conePointsFunctor_map_hom (hD : ∀ i, IsLimit (D.obj i))
    {c₁ c₂ : Cone (uncurry.obj F)} (α : c₁ ⟶ c₂) :
    ((D.conePointsFunctor hD).map α).hom = α.hom := sorry
/- Proof strategy: unfold the public functor and `Implementation.conePointsMap`. -/

end

end DiagramOfCones

end CategoryTheory.Limits
