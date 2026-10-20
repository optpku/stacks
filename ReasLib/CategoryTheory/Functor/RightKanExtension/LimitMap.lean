module

public import ReasLib.CategoryTheory.Limits.ChangeOfIndex
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps between pointwise right-Kan-extension limits

A morphism in the target category reindexes the corresponding structured-arrow categories.
This leaf specializes the general change-of-index comparison to their limits, records its
computation on projections, and gives limit coordinates for any chosen pointwise right Kan
extension.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightKanExtension

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {H : Type u₃} [Category.{v₃} H]
variable (L : C ⥤ D) (F : C ⥤ H)

/-- For a fully faithful functor, the counit of the chosen pointwise right Kan extension is an
isomorphism. The inverse is extracted from Mathlib's pointwise universal property, without a
family-wide right-Kan-extension hypothesis. -/
@[stacks 002L "counit isomorphism of a pointwise right Kan extension"]
noncomputable def counitIso [L.Full] [L.Faithful] [L.HasPointwiseRightKanExtension F] :
    L ⋙ L.rightKanExtension F ≅ F :=
  @asIso _ _ _ _ (rightKanExtensionCounit L F)
    ((isPointwiseRightKanExtensionOfIsRightKanExtension (F := F)
      (L.rightKanExtension F) (rightKanExtensionCounit L F)).isIso_hom)

/-- The map between pointwise right-Kan-extension limits induced by a morphism of target
objects. It is the general limit comparison for `StructuredArrow.map f`. -/
@[stacks 002L "map between pointwise right-Kan-extension limits"]
noncomputable def limitMap {X Y : D} (f : X ⟶ Y)
    [HasLimit (StructuredArrow.proj X L ⋙ F)]
    [HasLimit (StructuredArrow.proj Y L ⋙ F)] :
    limit (StructuredArrow.proj X L ⋙ F) ⟶
      limit (StructuredArrow.proj Y L ⋙ F) :=
  limitComparison (H := StructuredArrow.map f)
    (M := StructuredArrow.proj Y L ⋙ F)
    (N := StructuredArrow.proj X L ⋙ F) (𝟙 _)

/-- A pointwise right-Kan-extension limit map followed by a projection is the source
projection indexed by precomposition with the target morphism. -/
@[reassoc (attr := simp), stacks 002L "pointwise right-Kan-extension limit map on projections"]
theorem limitMap.π {X Y : D} (f : X ⟶ Y) (g : StructuredArrow Y L)
    [HasLimit (StructuredArrow.proj X L ⋙ F)]
    [HasLimit (StructuredArrow.proj Y L ⋙ F)] :
    limitMap L F f ≫ limit.π (StructuredArrow.proj Y L ⋙ F) g =
      limit.π (StructuredArrow.proj X L ⋙ F)
        ((StructuredArrow.map f).obj g) := sorry

/-- The pointwise right-Kan-extension limit map associated to an identity is the identity. -/
@[simp, stacks 002L "identity law for pointwise right-Kan-extension limit maps"]
theorem limitMap.id (X : D)
    [HasLimit (StructuredArrow.proj X L ⋙ F)] :
    limitMap L F (𝟙 X) = 𝟙 (limit (StructuredArrow.proj X L ⋙ F)) := sorry

/-- Pointwise right-Kan-extension limit maps respect composition. -/
@[stacks 002L "composition law for pointwise right-Kan-extension limit maps"]
theorem limitMap.comp {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasLimit (StructuredArrow.proj X L ⋙ F)]
    [HasLimit (StructuredArrow.proj Y L ⋙ F)]
    [HasLimit (StructuredArrow.proj Z L ⋙ F)] :
    limitMap L F (f ≫ g) = limitMap L F f ≫ limitMap L F g := sorry

/-- When all pointwise limits exist, `limitMap` is the structure map of Mathlib's explicit
pointwise right Kan extension functor. -/
@[stacks 002L "comparison with Mathlib's pointwise right Kan extension map"]
theorem limitMap.eq_pointwise [L.HasPointwiseRightKanExtension F]
    {X Y : D} (f : X ⟶ Y) :
    limitMap L F f = (L.pointwiseRightKanExtension F).map f := sorry

/-- Limit coordinates for the chosen right Kan extension when the extension is pointwise. -/
@[stacks 002L "chosen pointwise right Kan extension in limit coordinates"]
noncomputable def objIsoLimit [L.HasPointwiseRightKanExtension F] (X : D) :
    (L.rightKanExtension F).obj X ≅ limit (StructuredArrow.proj X L ⋙ F) :=
  RightExtension.IsPointwiseRightKanExtensionAt.isoLimit (F := F)
    (isPointwiseRightKanExtensionOfIsRightKanExtension (F := F)
      (L.rightKanExtension F) (rightKanExtensionCounit L F) X)

/-- The forward limit coordinate of the chosen pointwise right Kan extension computes by its
counit on every structured arrow. -/
@[reassoc (attr := simp), stacks 002L "chosen right Kan extension coordinate on projections"]
theorem objIsoLimit.hom_π [L.HasPointwiseRightKanExtension F]
    {X : D} (g : StructuredArrow X L) :
    (objIsoLimit L F X).hom ≫ limit.π (StructuredArrow.proj X L ⋙ F) g =
      (L.rightKanExtension F).map g.hom ≫
        (rightKanExtensionCounit L F).app g.right := sorry

/-- The inverse limit coordinate recovers every limit projection from the chosen right Kan
extension counit. -/
@[reassoc (attr := simp), stacks 002L "inverse chosen right Kan extension coordinate"]
theorem objIsoLimit.inv_π [L.HasPointwiseRightKanExtension F]
    {X : D} (g : StructuredArrow X L) :
    (objIsoLimit L F X).inv ≫ (L.rightKanExtension F).map g.hom ≫
        (rightKanExtensionCounit L F).app g.right =
      limit.π (StructuredArrow.proj X L ⋙ F) g := sorry

/-- In limit coordinates, the structure map of the chosen pointwise right Kan extension is
the map induced by `StructuredArrow.map f`. -/
@[stacks 002L "right Kan extension structure map in limit coordinates"]
theorem objIsoLimit.map [L.HasPointwiseRightKanExtension F]
    {X Y : D} (f : X ⟶ Y) :
    (objIsoLimit L F X).inv ≫ (L.rightKanExtension F).map f ≫
        (objIsoLimit L F Y).hom =
      limitMap L F f := sorry

/-- The structure map of the chosen pointwise right Kan extension followed by a limit
projection is the source projection at the reindexed structured arrow. -/
@[stacks 002L "right Kan extension structure map on limit projections"]
theorem objIsoLimit.map_π [L.HasPointwiseRightKanExtension F]
    {X Y : D} (f : X ⟶ Y)
    (g : StructuredArrow Y L) :
    (objIsoLimit L F X).inv ≫ (L.rightKanExtension F).map f ≫
          (objIsoLimit L F Y).hom ≫
        limit.π (StructuredArrow.proj Y L ⋙ F) g =
      limit.π (StructuredArrow.proj X L ⋙ F)
        ((StructuredArrow.map f).obj g) := sorry

end CategoryTheory.Functor.RightKanExtension

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {H : Type u₃} [Category.{v₃} H]
variable (L : C ⥤ D) (F : C ⥤ H)
variable [∀ G : C ⥤ H, L.HasRightKanExtension G]

/-- In Mathlib's canonical `ranObjObjIsoLimit` coordinates, the map of the right Kan extension
functor is the limit comparison induced by reindexing structured arrows. -/
@[stacks 002L "canonical right Kan extension map in limit coordinates"]
theorem ranObjObjIsoLimit_map [L.HasPointwiseRightKanExtension F]
    {X Y : D} (f : X ⟶ Y) :
    (L.ranObjObjIsoLimit F X).inv ≫ (L.ran.obj F).map f ≫
        (L.ranObjObjIsoLimit F Y).hom =
      RightKanExtension.limitMap L F f := sorry

/-- In Mathlib's canonical `ranObjObjIsoLimit` coordinates, a right Kan extension map followed
by a limit projection is the projection at the reindexed structured arrow. -/
@[stacks 002L "canonical right Kan extension map on limit projections"]
theorem ranObjObjIsoLimit_map_π [L.HasPointwiseRightKanExtension F]
    {X Y : D} (f : X ⟶ Y) (g : StructuredArrow Y L) :
    (L.ranObjObjIsoLimit F X).inv ≫ (L.ran.obj F).map f ≫
          (L.ranObjObjIsoLimit F Y).hom ≫
        limit.π (StructuredArrow.proj Y L ⋙ F) g =
      limit.π (StructuredArrow.proj X L ⋙ F)
        ((StructuredArrow.map f).obj g) := sorry

end CategoryTheory.Functor
