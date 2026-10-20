/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.LeftKanExtension.Map
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimits of individually chosen left Kan extensions

Left Kan extension is usually exposed as a functor only after every object in the source
functor category is known to admit an extension. This file supplies the objectwise layer: for a
single diagram, it only asks for the extensions of the objects occurring in that diagram and of
its colimit.

The colimit witness is constructed explicitly. A cocone over the chosen left Kan extensions is
restricted along the original functor and composed with the extension units; its source colimit
then descends through the universal property of the chosen left Kan extension. Thus no global
left-Kan-extension functor or family-wide extension hypothesis is required.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

namespace CategoryTheory.Functor.LeftKanExtension

variable {J : Type u₀} [Category.{v₀} J]
variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable (L : A ⥤ B)

namespace diagram

variable (K : J ⥤ (A ⥤ C)) [∀ j, L.HasLeftKanExtension (K.obj j)]

/-- The objectwise chosen left Kan extension assignment preserves identity maps. -/
@[stacks 018C "identity law for the diagram of chosen left Kan extensions"]
theorem map_id (j : J) :
    map L (K.map (𝟙 j)) = 𝟙 (L.leftKanExtension (K.obj j)) := sorry

/-- The objectwise chosen left Kan extension assignment preserves composition. -/
@[stacks 018C "composition law for the diagram of chosen left Kan extensions"]
theorem map_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    map L (K.map (f ≫ g)) = map L (K.map f) ≫ map L (K.map g) := sorry

end diagram

/-- The diagram formed by individually choosing a left Kan extension at every object of `K`.
No left Kan extensions away from the objects of `K` are required. -/
@[stacks 018C "diagram of individually chosen left Kan extensions"]
noncomputable def diagram (K : J ⥤ (A ⥤ C))
    [∀ j, L.HasLeftKanExtension (K.obj j)] : J ⥤ (B ⥤ C) where
  obj j := L.leftKanExtension (K.obj j)
  map f := map L (K.map f)
  map_id j := diagram.map_id L K j
  map_comp f g := diagram.map_comp L K f g

namespace diagram

variable {K K' : J ⥤ (A ⥤ C)}
variable [∀ j, L.HasLeftKanExtension (K.obj j)]
variable [∀ j, L.HasLeftKanExtension (K'.obj j)]

/-- The componentwise maps of chosen left Kan extensions satisfy naturality over the diagram
index. -/
@[stacks 018C "naturality of a map of chosen-left-Kan-extension diagrams",
  stacks 018D "naturality of a map of chosen-left-Kan-extension pushout diagrams"]
theorem map_naturality (η : K ⟶ K') {i j : J} (f : i ⟶ j) :
    (diagram L K).map f ≫ Functor.LeftKanExtension.map L (η.app j) =
      Functor.LeftKanExtension.map L (η.app i) ≫ (diagram L K').map f := sorry

/-- A natural transformation of source diagrams induces the componentwise natural
transformation between their diagrams of chosen left Kan extensions. -/
@[stacks 018C "map of chosen-left-Kan-extension diagrams",
  stacks 018D "map of chosen-left-Kan-extension pushout diagrams"]
noncomputable def map (η : K ⟶ K') : diagram L K ⟶ diagram L K' where
  app j := Functor.LeftKanExtension.map L (η.app j)
  naturality _ _ f := map_naturality L η f

/-- The component of the induced map of chosen-left-Kan-extension diagrams is the chosen left
Kan extension map of the corresponding source component. -/
@[simp, stacks 018C "components of a map of chosen-left-Kan-extension diagrams",
  stacks 018D "components of a map of chosen-left-Kan-extension pushout diagrams"]
theorem map_app (η : K ⟶ K') (j : J) :
    (map L η).app j = Functor.LeftKanExtension.map L (η.app j) := sorry

namespace map

/-- The diagram map induced by an identity natural transformation is the identity. -/
@[simp, stacks 018C "identity map of chosen-left-Kan-extension diagrams"]
theorem id (K₁ : J ⥤ (A ⥤ C)) [∀ j, L.HasLeftKanExtension (K₁.obj j)] :
    diagram.map L (𝟙 K₁) = 𝟙 (diagram L K₁) := sorry

/-- Maps of chosen-left-Kan-extension diagrams preserve composition. -/
@[stacks 018C "composition of maps of chosen-left-Kan-extension diagrams"]
theorem comp {K'' : J ⥤ (A ⥤ C)}
    [∀ j, L.HasLeftKanExtension (K''.obj j)]
    (η : K ⟶ K') (θ : K' ⟶ K'') :
    diagram.map L (η ≫ θ) = diagram.map L η ≫ diagram.map L θ := sorry

end map
end diagram

namespace colimit

variable (K : J ⥤ (A ⥤ C)) [HasColimit K]
variable [∀ j, L.HasLeftKanExtension (K.obj j)]
variable [L.HasLeftKanExtension (Limits.colimit K)]

namespace cocone

/-- Naturality of the injections into the left Kan extension of the source colimit. -/
@[stacks 018C "naturality of left Kan extension colimit injections",
  stacks 018D "naturality of left Kan extension pushout injections"]
theorem naturality {j j' : J} (f : j ⟶ j') :
    (diagram L K).map f ≫ map L (Limits.colimit.ι K j') =
      map L (Limits.colimit.ι K j) ≫
        ((Functor.const J).obj (L.leftKanExtension (Limits.colimit K))).map f := sorry

end cocone

/-- The canonical cocone from the diagram of chosen left Kan extensions to the left Kan
extension of the source colimit. -/
@[stacks 018C "left Kan extension colimit cocone",
  stacks 018D "left Kan extension pushout cocone"]
noncomputable def cocone : Cocone (diagram L K) where
  pt := L.leftKanExtension (Limits.colimit K)
  ι :=
    { app := fun j ↦ map L (Limits.colimit.ι K j)
      naturality := fun _ _ f ↦ cocone.naturality L K f }

namespace sourceCocone

variable (s : Cocone (diagram L K))

/-- Naturality of the cocone over `K` obtained from a cocone over the chosen left Kan
extensions by composing their units with its legs. -/
@[stacks 018C "restricted cocone naturality for chosen left Kan extensions",
  stacks 018D "restricted pushout cocone naturality for chosen left Kan extensions"]
theorem naturality {j j' : J} (f : j ⟶ j') :
    K.map f ≫
        (L.leftKanExtensionUnit (K.obj j') ≫ L.whiskerLeft (s.ι.app j')) =
      (L.leftKanExtensionUnit (K.obj j) ≫ L.whiskerLeft (s.ι.app j)) ≫
        ((Functor.const J).obj (L ⋙ s.pt)).map f := sorry

end sourceCocone

/-- Restrict a cocone over the diagram of chosen left Kan extensions along `L` and compose its
legs with the left Kan extension units. -/
@[stacks 018C "source cocone of a chosen-left-Kan-extension cocone",
  stacks 018D "source pushout cocone of a chosen-left-Kan-extension cocone"]
noncomputable def sourceCocone (s : Cocone (diagram L K)) : Cocone K where
  pt := L ⋙ s.pt
  ι :=
    { app := fun j ↦
        L.leftKanExtensionUnit (K.obj j) ≫ L.whiskerLeft (s.ι.app j)
      naturality := fun _ _ f ↦ sourceCocone.naturality L K s f }

/-- The universal descent from the left Kan extension of the source colimit to a cocone over
the individually chosen left Kan extensions. -/
@[stacks 018C "descent from the left Kan extension colimit cocone",
  stacks 018D "descent from the left Kan extension pushout cocone"]
noncomputable def desc (s : Cocone (diagram L K)) :
    L.leftKanExtension (Limits.colimit K) ⟶ s.pt :=
  (L.leftKanExtension (Limits.colimit K)).descOfIsLeftKanExtension
    (L.leftKanExtensionUnit (Limits.colimit K)) s.pt
    (Limits.colimit.desc K (sourceCocone L K s))

/-- The universal descent from the left Kan extension colimit cocone has the prescribed
components. -/
@[stacks 018C "left Kan extension colimit descent on injections",
  stacks 018D "left Kan extension pushout descent on injections"]
theorem desc_fac (s : Cocone (diagram L K)) (j : J) :
    (cocone L K).ι.app j ≫ desc L K s = s.ι.app j := sorry

/-- A morphism out of the left Kan extension colimit cocone is determined by its components. -/
@[stacks 018C "uniqueness for the left Kan extension colimit cocone",
  stacks 018D "uniqueness for the left Kan extension pushout cocone"]
theorem desc_uniq (s : Cocone (diagram L K))
    (m : (cocone L K).pt ⟶ s.pt)
    (h : ∀ j, (cocone L K).ι.app j ≫ m = s.ι.app j) :
    m = desc L K s := sorry

/-- An individually chosen left Kan extension of a source colimit is a colimit of the
individually chosen left Kan extensions. -/
@[stacks 018C "individually chosen left Kan extensions preserve colimits",
  stacks 018D "individually chosen left Kan extensions preserve pushouts"]
noncomputable def isColimit : IsColimit (cocone L K) where
  desc := desc L K
  fac := desc_fac L K
  uniq := desc_uniq L K

/-- The canonical comparison from the chosen colimit of individually chosen left Kan
extensions to the left Kan extension of the source colimit. -/
@[stacks 018C "chosen left Kan extension colimit comparison",
  stacks 018D "chosen left Kan extension pushout comparison"]
noncomputable def iso [HasColimit (diagram L K)] :
    Limits.colimit (diagram L K) ≅ L.leftKanExtension (Limits.colimit K) :=
  IsColimit.coconePointUniqueUpToIso
    (CategoryTheory.Limits.colimit.isColimit (diagram L K)) (isColimit L K)

/-- A target-diagram colimit injection followed by the forward comparison is the map induced by
the corresponding source colimit injection. -/
@[reassoc (attr := simp), stacks 018C "left Kan extension colimit comparison on injections",
  stacks 018D "left Kan extension pushout comparison on injections"]
theorem ι_iso_hom [HasColimit (diagram L K)] (j : J) :
    Limits.colimit.ι (diagram L K) j ≫ (iso L K).hom =
      map L (Limits.colimit.ι K j) := sorry

/-- A map induced by a source colimit injection followed by the inverse comparison recovers the
corresponding target-diagram colimit injection. -/
@[reassoc (attr := simp), stacks 018C "inverse left Kan extension colimit comparison on injections",
  stacks 018D "inverse left Kan extension pushout comparison on injections"]
theorem map_ι_iso_inv [HasColimit (diagram L K)] (j : J) :
    map L (Limits.colimit.ι K j) ≫ (iso L K).inv =
      Limits.colimit.ι (diagram L K) j := sorry

section Naturality

variable {K₁ K₂ : J ⥤ (A ⥤ C)} [HasColimit K₁] [HasColimit K₂]
variable [∀ j, L.HasLeftKanExtension (K₁.obj j)]
variable [∀ j, L.HasLeftKanExtension (K₂.obj j)]
variable [L.HasLeftKanExtension (Limits.colimit K₁)]
variable [L.HasLeftKanExtension (Limits.colimit K₂)]
variable [HasColimit (diagram L K₁)] [HasColimit (diagram L K₂)]

/-- The forward left Kan extension colimit comparison is natural in the source diagram. -/
@[reassoc, stacks 018C "naturality of the left Kan extension colimit comparison",
  stacks 018D "naturality of the left Kan extension pushout comparison"]
theorem iso_hom_naturality (η : K₁ ⟶ K₂) :
    Limits.colimMap (diagram.map L η) ≫ (iso L K₂).hom =
      (iso L K₁).hom ≫ map L (Limits.colimMap η) := sorry

/-- The inverse left Kan extension colimit comparison is natural in the source diagram. -/
@[reassoc, stacks 018C "naturality of the inverse left Kan extension colimit comparison",
  stacks 018D "naturality of the inverse left Kan extension pushout comparison"]
theorem iso_inv_naturality (η : K₁ ⟶ K₂) :
    map L (Limits.colimMap η) ≫ (iso L K₂).inv =
      (iso L K₁).inv ≫ Limits.colimMap (diagram.map L η) := sorry

end Naturality

end colimit

namespace coprod

variable (F G : A ⥤ C) [HasBinaryCoproduct F G]
variable [L.HasLeftKanExtension F] [L.HasLeftKanExtension G]
variable [L.HasLeftKanExtension (F ⨿ G)]

/-- The binary cofan whose point is the chosen left Kan extension of `F ⨿ G` and whose legs
are induced by the two coproduct injections. -/
@[stacks 018C "coproduct cocone for individually chosen left Kan extensions"]
noncomputable def cocone :
    BinaryCofan (L.leftKanExtension F) (L.leftKanExtension G) :=
  BinaryCofan.mk
    (map L (F := F) (G := F ⨿ G) (Limits.coprod.inl : F ⟶ F ⨿ G))
    (map L (F := G) (G := F ⨿ G) (Limits.coprod.inr : G ⟶ F ⨿ G))

/-- The source-coproduct morphism associated to two morphisms out of chosen left Kan
extensions. Its components use the two units before restriction along `L`. -/
@[stacks 018C "source coproduct map for chosen left Kan extensions"]
noncomputable def sourceDesc {T : B ⥤ C}
    (f : L.leftKanExtension F ⟶ T) (g : L.leftKanExtension G ⟶ T) :
    F ⨿ G ⟶ L ⋙ T :=
  Limits.coprod.desc
    (L.leftKanExtensionUnit F ≫ L.whiskerLeft f)
    (L.leftKanExtensionUnit G ≫ L.whiskerLeft g)

/-- The universal descent from the left Kan extension of a coproduct to a common target. -/
@[stacks 018C "descent from the left Kan extension of a coproduct"]
noncomputable def desc {T : B ⥤ C}
    (f : L.leftKanExtension F ⟶ T) (g : L.leftKanExtension G ⟶ T) :
    L.leftKanExtension (F ⨿ G) ⟶ T :=
  (L.leftKanExtension (F ⨿ G)).descOfIsLeftKanExtension
    (L.leftKanExtensionUnit (F ⨿ G)) T (sourceDesc L F G f g)

/-- The left coproduct injection followed by the universal descent is its first prescribed
component. -/
@[stacks 018C "left Kan extension coproduct descent on the left injection"]
theorem inl_desc {T : B ⥤ C}
    (f : L.leftKanExtension F ⟶ T) (g : L.leftKanExtension G ⟶ T) :
    (cocone L F G).inl ≫ desc L F G f g = f := sorry

/-- The right coproduct injection followed by the universal descent is its second prescribed
component. -/
@[stacks 018C "left Kan extension coproduct descent on the right injection"]
theorem inr_desc {T : B ⥤ C}
    (f : L.leftKanExtension F ⟶ T) (g : L.leftKanExtension G ⟶ T) :
    (cocone L F G).inr ≫ desc L F G f g = g := sorry

/-- A morphism out of the left Kan extension of a coproduct is determined by its two
components. -/
@[stacks 018C "uniqueness of the left Kan extension coproduct descent"]
theorem desc_uniq {T : B ⥤ C}
    (f : L.leftKanExtension F ⟶ T) (g : L.leftKanExtension G ⟶ T)
    (m : (cocone L F G).pt ⟶ T)
    (h_inl : (cocone L F G).inl ≫ m = f)
    (h_inr : (cocone L F G).inr ≫ m = g) :
    m = desc L F G f g := sorry

/-- The left Kan extension of a source coproduct is a coproduct of the individually chosen left
Kan extensions. -/
@[stacks 018C "individually chosen left Kan extensions preserve binary coproducts"]
noncomputable def isColimit : IsColimit (cocone L F G) :=
  BinaryCofan.IsColimit.mk (cocone L F G) (desc L F G)
    (inl_desc L F G) (inr_desc L F G) (desc_uniq L F G)

/-- The canonical binary-coproduct comparison for individually chosen left Kan extensions. -/
@[stacks 018C "binary-coproduct comparison for chosen left Kan extensions"]
noncomputable def iso
    [HasBinaryCoproduct (L.leftKanExtension F) (L.leftKanExtension G)] :
    L.leftKanExtension F ⨿ L.leftKanExtension G ≅
      L.leftKanExtension (F ⨿ G) :=
  IsColimit.coconePointUniqueUpToIso
    (CategoryTheory.Limits.colimit.isColimit
      (Limits.pair (L.leftKanExtension F) (L.leftKanExtension G)))
    (isColimit L F G)

/-- The target left coproduct injection followed by the comparison is the map induced by the
source left injection. -/
@[reassoc (attr := simp), stacks 018C "coproduct comparison on the left injection"]
theorem inl_iso_hom
    [HasBinaryCoproduct (L.leftKanExtension F) (L.leftKanExtension G)] :
    (Limits.coprod.inl : L.leftKanExtension F ⟶
      L.leftKanExtension F ⨿ L.leftKanExtension G) ≫ (iso L F G).hom =
      map L (Limits.coprod.inl : F ⟶ F ⨿ G) := sorry

/-- The target right coproduct injection followed by the comparison is the map induced by the
source right injection. -/
@[reassoc (attr := simp), stacks 018C "coproduct comparison on the right injection"]
theorem inr_iso_hom
    [HasBinaryCoproduct (L.leftKanExtension F) (L.leftKanExtension G)] :
    (Limits.coprod.inr : L.leftKanExtension G ⟶
      L.leftKanExtension F ⨿ L.leftKanExtension G) ≫ (iso L F G).hom =
      map L (Limits.coprod.inr : G ⟶ F ⨿ G) := sorry

/-- The map induced by the source left injection followed by the inverse coproduct comparison
recovers the chosen target left injection. -/
@[reassoc (attr := simp), stacks 018C "inverse coproduct comparison on the left injection"]
theorem map_inl_iso_inv
    [HasBinaryCoproduct (L.leftKanExtension F) (L.leftKanExtension G)] :
    map L (Limits.coprod.inl : F ⟶ F ⨿ G) ≫ (iso L F G).inv =
      Limits.coprod.inl := sorry

/-- The map induced by the source right injection followed by the inverse coproduct comparison
recovers the chosen target right injection. -/
@[reassoc (attr := simp), stacks 018C "inverse coproduct comparison on the right injection"]
theorem map_inr_iso_inv
    [HasBinaryCoproduct (L.leftKanExtension F) (L.leftKanExtension G)] :
    map L (Limits.coprod.inr : G ⟶ F ⨿ G) ≫ (iso L F G).inv =
      Limits.coprod.inr := sorry

end coprod

namespace pushout

variable {X Y Z : A ⥤ C} (f : Z ⟶ X) (g : Z ⟶ Y)
variable [HasPushout f g]
variable [L.HasLeftKanExtension X] [L.HasLeftKanExtension Y]
variable [L.HasLeftKanExtension Z]
variable [L.HasLeftKanExtension (Limits.pushout f g)]

/-- The maps induced by the two source pushout injections satisfy the target pushout
condition. -/
@[stacks 018D "pushout condition for chosen left Kan extension maps"]
theorem condition :
    map L f ≫ map L (Limits.pushout.inl f g) =
      map L g ≫ map L (Limits.pushout.inr f g) := sorry

/-- The pushout cocone whose point is the chosen left Kan extension of the source pushout. -/
@[stacks 018D "pushout cocone for individually chosen left Kan extensions"]
noncomputable def cocone : PushoutCocone (map L f) (map L g) :=
  PushoutCocone.mk
    (map L (Limits.pushout.inl f g))
    (map L (Limits.pushout.inr f g)) (condition L f g)

namespace sourceDesc

/-- Composing a target pushout cocone with the chosen left Kan extension units gives a
compatible pair of maps from the source span. -/
@[stacks 018D "source pushout condition for a chosen-left-Kan-extension cocone"]
theorem condition (s : PushoutCocone (map L f) (map L g)) :
    f ≫ (L.leftKanExtensionUnit X ≫ L.whiskerLeft s.inl) =
      g ≫ (L.leftKanExtensionUnit Y ≫ L.whiskerLeft s.inr) := sorry

end sourceDesc

/-- The map from the source pushout obtained by composing a target pushout cocone with the
chosen left Kan extension units. -/
@[stacks 018D "source pushout map for chosen left Kan extensions"]
noncomputable def sourceDesc (s : PushoutCocone (map L f) (map L g)) :
    Limits.pushout f g ⟶ L ⋙ s.pt :=
  Limits.pushout.desc
    (L.leftKanExtensionUnit X ≫ L.whiskerLeft s.inl)
    (L.leftKanExtensionUnit Y ≫ L.whiskerLeft s.inr)
    (sourceDesc.condition L f g s)

/-- The universal descent from the left Kan extension of a pushout to a target pushout
cocone. -/
@[stacks 018D "descent from the left Kan extension of a pushout"]
noncomputable def desc (s : PushoutCocone (map L f) (map L g)) :
    L.leftKanExtension (Limits.pushout f g) ⟶ s.pt :=
  (L.leftKanExtension (Limits.pushout f g)).descOfIsLeftKanExtension
    (L.leftKanExtensionUnit (Limits.pushout f g)) s.pt
    (sourceDesc L f g s)

/-- The left pushout injection followed by the universal descent is its prescribed component. -/
@[stacks 018D "left Kan extension pushout descent on the left injection"]
theorem inl_desc (s : PushoutCocone (map L f) (map L g)) :
    (cocone L f g).inl ≫ desc L f g s = s.inl := sorry

/-- The right pushout injection followed by the universal descent is its prescribed
component. -/
@[stacks 018D "left Kan extension pushout descent on the right injection"]
theorem inr_desc (s : PushoutCocone (map L f) (map L g)) :
    (cocone L f g).inr ≫ desc L f g s = s.inr := sorry

/-- A morphism out of the left Kan extension of a pushout is determined by its two
components. -/
@[stacks 018D "uniqueness of the left Kan extension pushout descent"]
theorem desc_uniq (s : PushoutCocone (map L f) (map L g))
    (m : (cocone L f g).pt ⟶ s.pt)
    (h_inl : (cocone L f g).inl ≫ m = s.inl)
    (h_inr : (cocone L f g).inr ≫ m = s.inr) :
    m = desc L f g s := sorry

/-- The left Kan extension of a source pushout is a pushout of the three individually chosen
left Kan extensions. -/
@[stacks 018D "individually chosen left Kan extensions preserve pushouts"]
noncomputable def isColimit : IsColimit (cocone L f g) :=
  PushoutCocone.IsColimit.mk (condition L f g) (desc L f g)
    (inl_desc L f g) (inr_desc L f g) (desc_uniq L f g)

/-- The canonical pushout comparison for individually chosen left Kan extensions. -/
@[stacks 018D "pushout comparison for chosen left Kan extensions"]
noncomputable def iso [HasPushout (map L f) (map L g)] :
    Limits.pushout (map L f) (map L g) ≅
      L.leftKanExtension (Limits.pushout f g) :=
  IsColimit.coconePointUniqueUpToIso
    (Limits.pushout.isColimit (map L f) (map L g)) (isColimit L f g)

/-- The target left pushout injection followed by the comparison is the map induced by the
source left pushout injection. -/
@[reassoc (attr := simp), stacks 018D "pushout comparison on the left injection"]
theorem inl_iso_hom [HasPushout (map L f) (map L g)] :
    Limits.pushout.inl (map L f) (map L g) ≫ (iso L f g).hom =
      map L (Limits.pushout.inl f g) := sorry

/-- The target right pushout injection followed by the comparison is the map induced by the
source right pushout injection. -/
@[reassoc (attr := simp), stacks 018D "pushout comparison on the right injection"]
theorem inr_iso_hom [HasPushout (map L f) (map L g)] :
    Limits.pushout.inr (map L f) (map L g) ≫ (iso L f g).hom =
      map L (Limits.pushout.inr f g) := sorry

/-- The map induced by the source left pushout injection followed by the inverse comparison
recovers the chosen target left injection. -/
@[reassoc (attr := simp), stacks 018D "inverse pushout comparison on the left injection"]
theorem map_inl_iso_inv [HasPushout (map L f) (map L g)] :
    map L (Limits.pushout.inl f g) ≫ (iso L f g).inv =
      Limits.pushout.inl (map L f) (map L g) := sorry

/-- The map induced by the source right pushout injection followed by the inverse comparison
recovers the chosen target right injection. -/
@[reassoc (attr := simp), stacks 018D "inverse pushout comparison on the right injection"]
theorem map_inr_iso_inv [HasPushout (map L f) (map L g)] :
    map L (Limits.pushout.inr f g) ≫ (iso L f g).inv =
      Limits.pushout.inr (map L f) (map L g) := sorry

end pushout

end CategoryTheory.Functor.LeftKanExtension
