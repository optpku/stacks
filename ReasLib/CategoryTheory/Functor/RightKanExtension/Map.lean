module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps between individually chosen right Kan extensions

The universal property of a chosen right Kan extension sends a natural transformation between
source functors to a morphism between their chosen extensions.  This file provides that
assumption-minimal operation and its identity, composition, and counit equations.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightKanExtension

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable (L : A ⥤ B)

/-- The universal lift to an individually chosen right Kan extension. -/
@[stacks 002L "lift to an individually chosen right Kan extension"]
noncomputable def lift (F : A ⥤ C) [L.HasRightKanExtension F]
    (T : B ⥤ C) (β : L ⋙ T ⟶ F) :
    T ⟶ L.rightKanExtension F :=
  (L.rightKanExtension F).liftOfIsRightKanExtension
    (L.rightKanExtensionCounit F) T β

/-- A universal lift followed by the chosen right-Kan-extension counit recovers its defining
natural transformation. -/
@[reassoc (attr := simp), stacks 002L "right Kan extension lift on the counit"]
theorem lift.counit (F : A ⥤ C) [L.HasRightKanExtension F]
    (T : B ⥤ C) (β : L ⋙ T ⟶ F) :
    L.whiskerLeft (lift L F T β) ≫ L.rightKanExtensionCounit F = β := sorry

/-- The universal Hom-equivalence of an individually chosen right Kan extension. -/
@[stacks 002L "Hom equivalence of an individually chosen right Kan extension"]
noncomputable def homEquiv (F : A ⥤ C) [L.HasRightKanExtension F]
    (T : B ⥤ C) :
    (T ⟶ L.rightKanExtension F) ≃ (L ⋙ T ⟶ F) :=
  (L.rightKanExtension F).homEquivOfIsRightKanExtension
    (L.rightKanExtensionCounit F) T

/-- The forward right-Kan-extension Hom-equivalence is restriction followed by the counit. -/
@[simp, stacks 002L "forward right Kan extension Hom equivalence"]
theorem homEquiv.apply (F : A ⥤ C) [L.HasRightKanExtension F]
    (T : B ⥤ C) (f : T ⟶ L.rightKanExtension F) :
    homEquiv L F T f = L.whiskerLeft f ≫ L.rightKanExtensionCounit F := sorry

/-- The inverse right-Kan-extension Hom-equivalence is the universal lift. -/
@[simp, stacks 002L "inverse right Kan extension Hom equivalence"]
theorem homEquiv.symm_apply (F : A ⥤ C) [L.HasRightKanExtension F]
    (T : B ⥤ C) (β : L ⋙ T ⟶ F) :
    (homEquiv L F T).symm β = lift L F T β := sorry

/-- A morphism between individually chosen right Kan extensions, obtained from the target
extension's universal property. -/
@[stacks 002L "map between individually chosen right Kan extensions",
  stacks 018C "map between individually chosen right Kan extensions"]
noncomputable def map {F G : A ⥤ C}
    [L.HasRightKanExtension F] [L.HasRightKanExtension G] (f : F ⟶ G) :
    L.rightKanExtension F ⟶ L.rightKanExtension G :=
  lift L G (L.rightKanExtension F) (L.rightKanExtensionCounit F ≫ f)

/-- The map between chosen right Kan extensions commutes with their counits. -/
@[reassoc (attr := simp), stacks 018C "chosen right Kan extension map and counit"]
theorem map_counit {F G : A ⥤ C}
    [L.HasRightKanExtension F] [L.HasRightKanExtension G] (f : F ⟶ G) :
    L.whiskerLeft (map L f) ≫ L.rightKanExtensionCounit G =
      L.rightKanExtensionCounit F ≫ f := sorry

/-- The chosen right Kan extension map associated to an identity is the identity. -/
@[simp, stacks 018C "identity map between chosen right Kan extensions"]
theorem map_id (F : A ⥤ C) [L.HasRightKanExtension F] :
    map L (𝟙 F) = 𝟙 (L.rightKanExtension F) := sorry

/-- Maps between individually chosen right Kan extensions respect composition. -/
@[stacks 018C "composition of maps between chosen right Kan extensions"]
theorem map_comp {F G H : A ⥤ C}
    [L.HasRightKanExtension F] [L.HasRightKanExtension G]
    [L.HasRightKanExtension H] (f : F ⟶ G) (g : G ⟶ H) :
    map L (f ≫ g) = map L f ≫ map L g := sorry

end CategoryTheory.Functor.RightKanExtension
