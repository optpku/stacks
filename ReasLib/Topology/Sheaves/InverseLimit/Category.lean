module

public import Mathlib.CategoryTheory.Category.Cat
public import ReasLib.Topology.Sheaves.InverseLimit.System
public import ReasLib.Topology.Sheaves.Pushforward.SectionFamilies

/-!
# Morphisms of compatible sheaf systems

This module equips compatible inverse-limit sheaf systems with their stagewise morphisms and
category structure, together with the compatible section-family view of a transition map.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open TopCat.Sheaf

noncomputable section

universe u v w

namespace TopCat.Sheaf.InverseLimit

variable {C : Type (w + 1)} [Category.{w} C]
variable {I : Type u} [Category.{v} I] {F : I ⥤ TopCat.{w}}

namespace SheafSystem

/-- A transition map is equivalently a compatible family of maps on sections. -/
def mapFamily (S : SheafSystem (C := C) F) {j i : I} (a : j ⟶ i) :
    TopCat.Sheaf.ContinuousMapSheafMapFamily (F.map a) (S.stageSheaf i) (S.stageSheaf j) :=
  TopCat.Presheaf.PushforwardHomFamily.ofHom (S.stageMap a).hom

/-- A morphism of compatible sheaf systems is a family of stagewise sheaf morphisms commuting with
the transition morphisms. -/
structure Hom (S T : SheafSystem (C := C) F) where
  /-- The component sheaf morphism at each stage. -/
  app : ∀ i : I, S.stageSheaf i ⟶ T.stageSheaf i
  /-- Naturality with respect to the transition morphisms. -/
  naturality : ∀ {j i : I} (a : j ⟶ i),
    S.stageMap a ≫ (TopCat.Sheaf.pushforward C (F.map a)).map (app j) = app i ≫ T.stageMap a

/-- Build a morphism of compatible sheaf systems from stagewise maps satisfying naturality. -/
def homMk {S T : SheafSystem (C := C) F} (app : ∀ i : I, S.stageSheaf i ⟶ T.stageSheaf i)
    (naturality : ∀ {j i : I} (a : j ⟶ i),
      S.stageMap a ≫ (TopCat.Sheaf.pushforward C (F.map a)).map (app j) = app i ≫ T.stageMap a) :
    Hom S T where
  app := app
  naturality := naturality

/-- The identity morphism of a compatible sheaf system. -/
def Hom.id (S : SheafSystem (C := C) F) : Hom S S :=
  homMk (fun i ↦ 𝟙 (S.stageSheaf i)) sorry

/-- Composition of morphisms of compatible sheaf systems. -/
def Hom.comp {S T U : SheafSystem (C := C) F} (α : Hom S T) (β : Hom T U) : Hom S U :=
  homMk (fun i ↦ α.app i ≫ β.app i) sorry

/-- The stagewise component of `homMk app naturality` is `app`. -/
theorem homMk_app {S T : SheafSystem (C := C) F}
    (app : ∀ i : I, S.stageSheaf i ⟶ T.stageSheaf i)
    (naturality : ∀ {j i : I} (a : j ⟶ i),
      S.stageMap a ≫ (TopCat.Sheaf.pushforward C (F.map a)).map (app j) = app i ≫ T.stageMap a) :
    (homMk app naturality).app = app := sorry

/-- The category of compatible sheaf systems on a diagram of spaces. -/
@[reducible] def category : Category (SheafSystem (C := C) F) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The bundled category of compatible sheaf systems over `F`. -/
def asCategory : Cat where
  α := SheafSystem (C := C) F
  str := SheafSystem.category

end SheafSystem

end TopCat.Sheaf.InverseLimit
