/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Limit.DirectedAffine

/-!
# Point closures in directed affine-transition limits

This file constructs the residue-field cocone and the reduced point-closure
cones associated to a point of a limiting cone of schemes.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Limit.DirectedAffine

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D)
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]

/-- The residue-field map attached to a transition between the images of a point in a cone. -/
noncomputable def pointResidueFieldMap (s : c.pt)
    {i j : (OrderDual I)ᵒᵖ} (f : i ⟶ j) :
    (D.obj i.unop).residueField ((c.π.app i.unop) s) ⟶
      (D.obj j.unop).residueField ((c.π.app j.unop) s) :=
  ((D.obj i.unop).residueFieldCongr
      (by
        have h := congrArg (fun g : c.pt ⟶ D.obj i.unop ↦ g s) (c.w f.unop)
        change (D.map f.unop) ((c.π.app j.unop) s) = (c.π.app i.unop) s at h
        exact h)).inv ≫
    (D.map f.unop).residueFieldMap ((c.π.app j.unop) s)

set_option backward.isDefEq.respectTransparency false in
private theorem pointResidueFieldMap_toLimit (s : c.pt)
    {i j : (OrderDual I)ᵒᵖ} (f : i ⟶ j) :
    pointResidueFieldMap D c s f ≫ (c.π.app j.unop).residueFieldMap s =
      (c.π.app i.unop).residueFieldMap s := by
  unfold pointResidueFieldMap
  rw [Category.assoc, ← Scheme.residueFieldMap_comp,
    Scheme.Hom.residueFieldMap_congr (c.w f.unop)]
  simp

/-- The residue-field map of an identity transition is the identity. -/
theorem pointResidueFieldMap_id (s : c.pt) (i : (OrderDual I)ᵒᵖ) :
    pointResidueFieldMap D c s (𝟙 i) = 𝟙 _ := by
  have : Mono ((c.π.app i.unop).residueFieldMap s) :=
    ConcreteCategory.mono_of_injective _
      ((c.π.app i.unop).residueFieldMap s).hom.injective
  apply (cancel_mono ((c.π.app i.unop).residueFieldMap s)).mp
  exact (pointResidueFieldMap_toLimit D c s (𝟙 i)).trans (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Residue-field maps attached to transitions preserve composition. -/
theorem pointResidueFieldMap_comp (s : c.pt)
    {i j k : (OrderDual I)ᵒᵖ} (f : i ⟶ j) (g : j ⟶ k) :
    pointResidueFieldMap D c s (f ≫ g) =
      pointResidueFieldMap D c s f ≫ pointResidueFieldMap D c s g := by
  have : Mono ((c.π.app k.unop).residueFieldMap s) :=
    ConcreteCategory.mono_of_injective _
      ((c.π.app k.unop).residueFieldMap s).hom.injective
  apply (cancel_mono ((c.π.app k.unop).residueFieldMap s)).mp
  rw [pointResidueFieldMap_toLimit, Category.assoc, pointResidueFieldMap_toLimit,
    pointResidueFieldMap_toLimit]

/-- The diagram of residue fields of the stagewise images of a point. -/
noncomputable def pointResidueFieldDiagram (s : c.pt) :
    (OrderDual I)ᵒᵖ ⥤ CommRingCat.{u} where
  obj i := (D.obj i.unop).residueField ((c.π.app i.unop) s)
  map f := pointResidueFieldMap D c s f
  map_id i := pointResidueFieldMap_id D c s i
  map_comp f g := pointResidueFieldMap_comp D c s f g

/-- The residue-field map from a stagewise point to the residue field of the limiting point. -/
noncomputable def pointResidueFieldToLimit (s : c.pt) (i : (OrderDual I)ᵒᵖ) :
    (pointResidueFieldDiagram D c s).obj i ⟶ c.pt.residueField s :=
  (c.π.app i.unop).residueFieldMap s

/-- The residue-field maps to the limiting point are natural in the stage. -/
theorem pointResidueFieldToLimit_naturality (s : c.pt)
    {i j : (OrderDual I)ᵒᵖ} (f : i ⟶ j) :
    (pointResidueFieldDiagram D c s).map f ≫ pointResidueFieldToLimit D c s j =
      pointResidueFieldToLimit D c s i := by
  exact pointResidueFieldMap_toLimit D c s f

/-- The canonical cocone from the stagewise residue fields to the residue field of the
limiting point. -/
noncomputable def pointResidueFieldCocone (s : c.pt) :
    Cocone (pointResidueFieldDiagram D c s) where
  pt := c.pt.residueField s
  ι :=
    { app := pointResidueFieldToLimit D c s
      naturality := fun _ _ f ↦ pointResidueFieldToLimit_naturality D c s f }

/-- The reduced point-closure morphism attached to a transition in the inverse system. -/
noncomputable def pointClosureSchemeMap (s : c.pt)
    {i j : OrderDual I} (f : i ⟶ j) :
    PointClosure.scheme ((c.π.app i) s) ⟶ PointClosure.scheme ((c.π.app j) s) :=
  PointClosure.mapOfEq (D.map f) ((c.π.app i) s) ((c.π.app j) s)
    (by
      have h := congrArg (fun g : c.pt ⟶ D.obj j ↦ g s) (c.w f)
      change (D.map f) ((c.π.app i) s) = (c.π.app j) s at h
      exact h)

private theorem pointClosureMapOfEq_ι {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (h : f x = y) :
    PointClosure.mapOfEq f x y h ≫ PointClosure.ι y = PointClosure.ι x ≫ f := by
  subst y
  change (PointClosure.map f x ≫ 𝟙 _) ≫ PointClosure.ι (f x) = _
  rw [Category.comp_id]
  exact IdealSheafData.subschemeMap_subschemeι _ _ f _

/-- The reduced point-closure map of an identity transition is the identity. -/
theorem pointClosureSchemeMap_id (s : c.pt) (i : OrderDual I) :
    pointClosureSchemeMap D c s (𝟙 i) = 𝟙 _ := by
  apply (cancel_mono (PointClosure.ι ((c.π.app i) s))).mp
  dsimp only [pointClosureSchemeMap]
  rw [pointClosureMapOfEq_ι]
  simp

/-- Reduced point-closure maps attached to transitions preserve composition. -/
theorem pointClosureSchemeMap_comp (s : c.pt)
    {i j k : OrderDual I} (f : i ⟶ j) (g : j ⟶ k) :
    pointClosureSchemeMap D c s (f ≫ g) =
      pointClosureSchemeMap D c s f ≫ pointClosureSchemeMap D c s g := by
  apply (cancel_mono (PointClosure.ι ((c.π.app k) s))).mp
  dsimp only [pointClosureSchemeMap]
  rw [pointClosureMapOfEq_ι, Category.assoc, pointClosureMapOfEq_ι,
    ← Category.assoc, pointClosureMapOfEq_ι, Category.assoc, D.map_comp]

/-- The inverse diagram of reduced closures of the stagewise images of a point. -/
noncomputable def pointClosureSchemeDiagram (s : c.pt) : OrderDual I ⥤ Scheme.{u} where
  obj i := PointClosure.scheme ((c.π.app i) s)
  map f := pointClosureSchemeMap D c s f
  map_id i := pointClosureSchemeMap_id D c s i
  map_comp f g := pointClosureSchemeMap_comp D c s f g

/-- The canonical map from the reduced closure of a limiting point to a stagewise closure. -/
noncomputable def pointClosureSchemeToStage (s : c.pt) (i : OrderDual I) :
    PointClosure.scheme s ⟶ (pointClosureSchemeDiagram D c s).obj i :=
  PointClosure.mapOfEq (c.π.app i) s ((c.π.app i) s) rfl

set_option backward.isDefEq.respectTransparency false in
/-- The maps from the reduced closure of the limiting point are natural in the stage. -/
theorem pointClosureSchemeToStage_naturality (s : c.pt)
    {i j : OrderDual I} (f : i ⟶ j) :
    pointClosureSchemeToStage D c s i ≫ (pointClosureSchemeDiagram D c s).map f =
      pointClosureSchemeToStage D c s j := by
  apply (cancel_mono (PointClosure.ι ((c.π.app j) s))).mp
  dsimp only [pointClosureSchemeToStage, pointClosureSchemeDiagram, pointClosureSchemeMap]
  rw [Category.assoc, pointClosureMapOfEq_ι, ← Category.assoc, pointClosureMapOfEq_ι,
    pointClosureMapOfEq_ι, Category.assoc, c.w f]

/-- The canonical cone of reduced point closures over the inverse system. -/
noncomputable def pointClosureSchemeCone (s : c.pt) :
    Cone (pointClosureSchemeDiagram D c s) where
  pt := PointClosure.scheme s
  π :=
    { app := pointClosureSchemeToStage D c s
      naturality := fun _ j f ↦
        (Category.id_comp (pointClosureSchemeToStage D c s j)).trans
          (pointClosureSchemeToStage_naturality D c s f).symm }

/-- The underlying-set diagram of the reduced closures of the stagewise points. -/
noncomputable def pointClosureSetDiagram (s : c.pt) : OrderDual I ⥤ Type u :=
  pointClosureSchemeDiagram D c s ⋙ Scheme.forget

/-- The underlying-set cone of the reduced closure of the limiting point. -/
noncomputable def pointClosureSetCone (s : c.pt) :
    Cone (pointClosureSetDiagram D c s) :=
  Scheme.forget.mapCone (pointClosureSchemeCone D c s)

/-- The stagewise residue fields form a colimit with vertex the residue field of the limiting
point. -/
theorem nonempty_isColimit_pointResidueFieldCocone (hc : IsLimit c) (s : c.pt) :
    Nonempty (IsColimit (pointResidueFieldCocone D c s)) := sorry

/-- The closure of a point in the limiting scheme is the limit of the stagewise point closures
as underlying sets. -/
theorem nonempty_isLimit_pointClosureSetCone (hc : IsLimit c) (s : c.pt) :
    Nonempty (IsLimit (pointClosureSetCone D c s)) := sorry

/-- The reduced induced scheme on the closure of a point in the limiting scheme is the limit
of the stagewise reduced point-closure schemes. -/
theorem nonempty_isLimit_pointClosureSchemeCone (hc : IsLimit c) (s : c.pt) :
    Nonempty (IsLimit (pointClosureSchemeCone D c s)) := sorry

end AlgebraicGeometry.Scheme.Limit.DirectedAffine
