/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps between individually chosen left Kan extensions

The universal property of a chosen left Kan extension sends a natural transformation between
source functors to a morphism between their chosen extensions.  This file provides that
assumption-minimal operation and its identity, composition, and unit equations.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.LeftKanExtension

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable (L : A ⥤ B)

/-- The universal descent map from an individually chosen left Kan extension. -/
@[stacks 002K "descent from an individually chosen left Kan extension"]
noncomputable def desc (F : A ⥤ C) [L.HasLeftKanExtension F]
    (T : B ⥤ C) (β : F ⟶ L ⋙ T) :
    L.leftKanExtension F ⟶ T :=
  (L.leftKanExtension F).descOfIsLeftKanExtension
    (L.leftKanExtensionUnit F) T β

/-- The chosen left-Kan-extension unit followed by a universal descent map recovers its defining
natural transformation. -/
@[reassoc (attr := simp), stacks 002K "left Kan extension unit followed by descent"]
theorem desc.unit (F : A ⥤ C) [L.HasLeftKanExtension F]
    (T : B ⥤ C) (β : F ⟶ L ⋙ T) :
    L.leftKanExtensionUnit F ≫ L.whiskerLeft (desc L F T β) = β := sorry

/-- The universal Hom-equivalence of an individually chosen left Kan extension. -/
@[stacks 002K "Hom equivalence of an individually chosen left Kan extension"]
noncomputable def homEquiv (F : A ⥤ C) [L.HasLeftKanExtension F]
    (T : B ⥤ C) :
    (L.leftKanExtension F ⟶ T) ≃ (F ⟶ L ⋙ T) :=
  (L.leftKanExtension F).homEquivOfIsLeftKanExtension
    (L.leftKanExtensionUnit F) T

/-- The forward left-Kan-extension Hom-equivalence is the unit followed by restriction. -/
@[simp, stacks 002K "forward left Kan extension Hom equivalence"]
theorem homEquiv.apply (F : A ⥤ C) [L.HasLeftKanExtension F]
    (T : B ⥤ C) (f : L.leftKanExtension F ⟶ T) :
    homEquiv L F T f = L.leftKanExtensionUnit F ≫ L.whiskerLeft f := sorry

/-- The inverse left-Kan-extension Hom-equivalence is the universal descent map. -/
@[simp, stacks 002K "inverse left Kan extension Hom equivalence"]
theorem homEquiv.symm_apply (F : A ⥤ C) [L.HasLeftKanExtension F]
    (T : B ⥤ C) (β : F ⟶ L ⋙ T) :
    (homEquiv L F T).symm β = desc L F T β := sorry

/-- A morphism between individually chosen left Kan extensions, obtained from the source
extension's universal property. -/
@[stacks 002K "map between individually chosen left Kan extensions"]
noncomputable def map {F G : A ⥤ C}
    [L.HasLeftKanExtension F] [L.HasLeftKanExtension G] (f : F ⟶ G) :
    L.leftKanExtension F ⟶ L.leftKanExtension G :=
  desc L F (L.leftKanExtension G) (f ≫ L.leftKanExtensionUnit G)

/-- The map between chosen left Kan extensions commutes with their units. -/
@[reassoc (attr := simp), stacks 002K "chosen left Kan extension map and unit"]
theorem unit_map {F G : A ⥤ C}
    [L.HasLeftKanExtension F] [L.HasLeftKanExtension G] (f : F ⟶ G) :
    L.leftKanExtensionUnit F ≫ L.whiskerLeft (map L f) =
      f ≫ L.leftKanExtensionUnit G := sorry

/-- The chosen left Kan extension map associated to an identity is the identity. -/
@[simp, stacks 002K "identity map between chosen left Kan extensions"]
theorem map_id (F : A ⥤ C) [L.HasLeftKanExtension F] :
    map L (𝟙 F) = 𝟙 (L.leftKanExtension F) := sorry

/-- Maps between individually chosen left Kan extensions respect composition. -/
@[stacks 002K "composition of maps between chosen left Kan extensions"]
theorem map_comp {F G H : A ⥤ C}
    [L.HasLeftKanExtension F] [L.HasLeftKanExtension G]
    [L.HasLeftKanExtension H] (f : F ⟶ G) (g : G ⟶ H) :
    map L (f ≫ g) = map L f ≫ map L g := sorry

end CategoryTheory.Functor.LeftKanExtension
