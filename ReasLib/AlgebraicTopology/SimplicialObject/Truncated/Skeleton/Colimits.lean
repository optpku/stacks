module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.CategoryTheory.Functor.LeftKanExtension.Colimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Objectwise skeleta and colimits

This file specializes the objectwise left-Kan-extension colimit API to skeleta of truncated
simplicial objects. The universal and map API is owned by `Truncated.KanExtension`; this leaf
only assumes the chosen skeleta needed by each colimit statement.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe v₀ v₁ u₀ u₁

namespace CategoryTheory.SimplicialObject.Truncated.skeleton

variable {J : Type u₀} [Category.{v₀} J]
variable {C : Type u₁} [Category.{v₁} C] {n : ℕ}

/-- The diagram obtained by taking the chosen skeleton of each object and the induced map of
each arrow. -/
@[stacks 018C "diagram of chosen objectwise skeleta"]
noncomputable abbrev diagram (K : J ⥤ SimplicialObject.Truncated C n)
    [∀ j, (K.obj j).HasSkeleton] : J ⥤ SimplicialObject C :=
  Functor.LeftKanExtension.diagram
    (SimplexCategory.Truncated.inclusion n).op K

namespace colimit

variable (K : J ⥤ SimplicialObject.Truncated C n) [HasColimit K]
variable [∀ j, (K.obj j).HasSkeleton]
variable [(Limits.colimit K).HasSkeleton]

/-- The canonical cocone from the diagram of chosen objectwise skeleta to the skeleton of the
source colimit. -/
@[stacks 018C "objectwise skeleton colimit cocone",
  stacks 018D "objectwise skeleton pushout cocone"]
noncomputable def cocone : Cocone (diagram K) :=
  Functor.LeftKanExtension.colimit.cocone
    (SimplexCategory.Truncated.inclusion n).op K

/-- The skeleton of a source colimit is a colimit of the chosen objectwise skeleta. -/
@[stacks 018C "objectwise skeleta preserve colimits",
  stacks 018D "objectwise skeleta preserve pushouts"]
noncomputable def isColimit : IsColimit (cocone K) :=
  Functor.LeftKanExtension.colimit.isColimit
    (SimplexCategory.Truncated.inclusion n).op K

/-- The canonical comparison between the chosen target colimit of objectwise skeleta and the
skeleton of the source colimit. -/
@[stacks 018C "objectwise skeleton colimit comparison",
  stacks 018D "objectwise skeleton pushout comparison"]
noncomputable def iso [HasColimit (diagram K)] :
    Limits.colimit (diagram K) ≅ (Limits.colimit K).skeleton :=
  Functor.LeftKanExtension.colimit.iso
    (SimplexCategory.Truncated.inclusion n).op K

/-- The forward skeleton colimit comparison computes on every colimit injection. -/
@[reassoc (attr := simp), stacks 018C "objectwise skeleton colimit comparison on injections",
  stacks 018D "objectwise skeleton pushout comparison on injections"]
theorem ι_iso_hom [HasColimit (diagram K)] (j : J) :
    Limits.colimit.ι (diagram K) j ≫ (iso K).hom =
      map (Limits.colimit.ι K j) := sorry

/-- The inverse skeleton colimit comparison recovers every target-colimit injection. -/
@[reassoc (attr := simp),
  stacks 018C "inverse objectwise skeleton colimit comparison on injections",
  stacks 018D "inverse objectwise skeleton pushout comparison on injections"]
theorem map_ι_iso_inv [HasColimit (diagram K)] (j : J) :
    map (Limits.colimit.ι K j) ≫ (iso K).inv =
      Limits.colimit.ι (diagram K) j := sorry

end colimit

namespace coprod

variable (U V : SimplicialObject.Truncated C n) [HasBinaryCoproduct U V]
variable [U.HasSkeleton] [V.HasSkeleton] [(U ⨿ V).HasSkeleton]

/-- The binary cofan exhibiting the skeleton of `U ⨿ V` as an objectwise coproduct. -/
@[stacks 018C "objectwise skeleton coproduct cocone"]
noncomputable def cocone : BinaryCofan U.skeleton V.skeleton :=
  Functor.LeftKanExtension.coprod.cocone
    (SimplexCategory.Truncated.inclusion n).op U V

/-- The skeleton of `U ⨿ V` is a coproduct of the chosen skeleta of `U` and `V`. -/
@[stacks 018C "objectwise skeleton coproduct colimit"]
noncomputable def isColimit : IsColimit (cocone U V) :=
  Functor.LeftKanExtension.coprod.isColimit
    (SimplexCategory.Truncated.inclusion n).op U V

/-- The canonical coproduct comparison for chosen objectwise skeleta. -/
@[stacks 018C "objectwise skeleton coproduct comparison"]
noncomputable def iso [HasBinaryCoproduct U.skeleton V.skeleton] :
    U.skeleton ⨿ V.skeleton ≅ (U ⨿ V).skeleton :=
  Functor.LeftKanExtension.coprod.iso
    (SimplexCategory.Truncated.inclusion n).op U V

/-- The left target injection followed by the coproduct comparison is induced by the source
left injection. -/
@[reassoc (attr := simp), stacks 018C "objectwise skeleton coproduct comparison left injection"]
theorem inl_iso_hom [HasBinaryCoproduct U.skeleton V.skeleton] :
    (Limits.coprod.inl : U.skeleton ⟶ U.skeleton ⨿ V.skeleton) ≫
        (iso U V).hom =
      map (Limits.coprod.inl : U ⟶ U ⨿ V) := sorry

/-- The right target injection followed by the coproduct comparison is induced by the source
right injection. -/
@[reassoc (attr := simp), stacks 018C "objectwise skeleton coproduct comparison right injection"]
theorem inr_iso_hom [HasBinaryCoproduct U.skeleton V.skeleton] :
    (Limits.coprod.inr : V.skeleton ⟶ U.skeleton ⨿ V.skeleton) ≫
        (iso U V).hom =
      map (Limits.coprod.inr : V ⟶ U ⨿ V) := sorry

/-- The induced source left injection followed by the inverse coproduct comparison recovers the
chosen target left injection. -/
@[reassoc (attr := simp), stacks 018C "inverse objectwise skeleton coproduct left injection"]
theorem map_inl_iso_inv [HasBinaryCoproduct U.skeleton V.skeleton] :
    map (Limits.coprod.inl : U ⟶ U ⨿ V) ≫ (iso U V).inv =
      Limits.coprod.inl := sorry

/-- The induced source right injection followed by the inverse coproduct comparison recovers the
chosen target right injection. -/
@[reassoc (attr := simp), stacks 018C "inverse objectwise skeleton coproduct right injection"]
theorem map_inr_iso_inv [HasBinaryCoproduct U.skeleton V.skeleton] :
    map (Limits.coprod.inr : V ⟶ U ⨿ V) ≫ (iso U V).inv =
      Limits.coprod.inr := sorry

end coprod

namespace pushout

variable {U V W : SimplicialObject.Truncated C n} (f : U ⟶ V) (g : U ⟶ W)
variable [HasPushout f g]
variable [U.HasSkeleton] [V.HasSkeleton] [W.HasSkeleton]
variable [(Limits.pushout f g).HasSkeleton]

/-- The maps induced by the source pushout injections satisfy the target pushout condition. -/
@[stacks 018D "objectwise skeleton pushout condition"]
theorem condition :
    map f ≫ map (Limits.pushout.inl f g) =
      map g ≫ map (Limits.pushout.inr f g) := sorry

/-- The pushout cocone whose point is the skeleton of the source pushout. -/
@[stacks 018D "objectwise skeleton pushout cocone"]
noncomputable def cocone : PushoutCocone (map f) (map g) :=
  Functor.LeftKanExtension.pushout.cocone
    (SimplexCategory.Truncated.inclusion n).op f g

/-- The skeleton of the source pushout is a pushout of the three chosen objectwise skeleta. -/
@[stacks 018D "objectwise skeleton pushout colimit"]
noncomputable def isColimit : IsColimit (cocone f g) :=
  Functor.LeftKanExtension.pushout.isColimit
    (SimplexCategory.Truncated.inclusion n).op f g

/-- The canonical pushout comparison for chosen objectwise skeleta. -/
@[stacks 018D "objectwise skeleton pushout comparison"]
noncomputable def iso [HasPushout (map f) (map g)] :
    Limits.pushout (map f) (map g) ≅ (Limits.pushout f g).skeleton :=
  Functor.LeftKanExtension.pushout.iso
    (SimplexCategory.Truncated.inclusion n).op f g

/-- The left target pushout injection followed by the comparison is induced by the source left
pushout injection. -/
@[reassoc (attr := simp), stacks 018D "objectwise skeleton pushout comparison left injection"]
theorem inl_iso_hom [HasPushout (map f) (map g)] :
    Limits.pushout.inl (map f) (map g) ≫ (iso f g).hom =
      map (Limits.pushout.inl f g) := sorry

/-- The right target pushout injection followed by the comparison is induced by the source
right pushout injection. -/
@[reassoc (attr := simp), stacks 018D "objectwise skeleton pushout comparison right injection"]
theorem inr_iso_hom [HasPushout (map f) (map g)] :
    Limits.pushout.inr (map f) (map g) ≫ (iso f g).hom =
      map (Limits.pushout.inr f g) := sorry

/-- The induced source left pushout injection followed by the inverse comparison recovers the
chosen target left injection. -/
@[reassoc (attr := simp), stacks 018D "inverse objectwise skeleton pushout left injection"]
theorem map_inl_iso_inv [HasPushout (map f) (map g)] :
    map (Limits.pushout.inl f g) ≫ (iso f g).inv =
      Limits.pushout.inl (map f) (map g) := sorry

/-- The induced source right pushout injection followed by the inverse comparison recovers the
chosen target right injection. -/
@[reassoc (attr := simp), stacks 018D "inverse objectwise skeleton pushout right injection"]
theorem map_inr_iso_inv [HasPushout (map f) (map g)] :
    map (Limits.pushout.inr f g) ≫ (iso f g).inv =
      Limits.pushout.inr (map f) (map g) := sorry

end pushout

end CategoryTheory.SimplicialObject.Truncated.skeleton
