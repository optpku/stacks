/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.Algebra.Category.Ring.Presheaf.Localization

/-!
# Localization of sheaves of commutative rings

The localization of a sheaf of commutative rings along a compatible family of submonoids is
modelled by sheafifying the explicit objectwise localization presheaf.  This file exposes the
canonical map and its universal property without repeating the objectwise construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Presheaf.SubmonoidPresheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Presheaf

variable {O : Cᵒᵖ ⥤ CommRingCat.{max u v}} (S : SubmonoidPresheaf O)

/-- The sheafification of the objectwise localization presheaf. -/
@[stacks 01D0 "sheafified localization presheaf", stacks 0EMC "localization sheaf"]
protected noncomputable def localizationSheaf : Sheaf J CommRingCat.{max u v} :=
  (presheafToSheaf J CommRingCat).obj S.localizationPresheaf

/-- The morphism between sheafifications induced by the canonical localization map. -/
@[stacks 01D0 "map between sheafifications"]
noncomputable def sheafificationMap :
    (presheafToSheaf J CommRingCat).obj O ⟶ S.localizationSheaf :=
  (presheafToSheaf J CommRingCat).map S.toLocalizationPresheaf

/-- The canonical presheaf morphism from the original presheaf to the underlying
presheaf of its sheafified localization. -/
noncomputable def toSheafifiedLocalization :
    O ⟶ (S.localizationSheaf (J := J)).obj :=
  toSheafify J O ≫ (S.sheafificationMap (J := J)).hom

/-- The sheafification of the canonical localization map inverts the distinguished
sections. -/
theorem toSheafifiedLocalization_mapsToUnits :
    S.MapsToUnits (S.toSheafifiedLocalization (J := J)) := sorry

namespace Sheafification

/-- A morphism from the sheafification of the original presheaf inverts the chosen
sections after composition with the sheafification unit. -/
@[stacks 01D0 "inverting distinguished sections after sheafification"]
def Inverts {A : Sheaf J CommRingCat.{max u v}}
    (f : (presheafToSheaf J CommRingCat).obj O ⟶ A) : Prop :=
  S.MapsToUnits (toSheafify J O ≫ f.hom)

/-- The canonical map between sheafifications inverts the chosen sections. -/
theorem sheafificationMap_inverts :
    Inverts S (S.sheafificationMap (J := J)) := sorry

/-- The presheaf-level lift underlying a map from the sheafified localization. -/
noncomputable def liftPresheaf {A : Sheaf J CommRingCat.{max u v}}
    (f : (presheafToSheaf J CommRingCat).obj O ⟶ A) (hf : Inverts S f) :
    S.localizationPresheaf ⟶ A.obj :=
  Universal.lift S (toSheafify J O ≫ f.hom) hf

/-- The canonical lift from the sheafified localization induced by a morphism which
inverts the chosen sections. -/
noncomputable def lift {A : Sheaf J CommRingCat.{max u v}}
    (f : (presheafToSheaf J CommRingCat).obj O ⟶ A) (hf : Inverts S f) :
    S.localizationSheaf ⟶ A :=
  ⟨sheafifyLift J (liftPresheaf S f hf) A.property⟩

/-- The sheafified-localization lift factors the original morphism. -/
@[reassoc]
theorem lift_fac {A : Sheaf J CommRingCat.{max u v}}
    (f : (presheafToSheaf J CommRingCat).obj O ⟶ A) (hf : Inverts S f) :
    S.sheafificationMap ≫ lift S f hf = f := sorry

/-- A morphism from the sheafified localization with the prescribed composite is the
canonical lift. -/
theorem lift_unique {A : Sheaf J CommRingCat.{max u v}}
    (f : (presheafToSheaf J CommRingCat).obj O ⟶ A) (hf : Inverts S f)
    (g : S.localizationSheaf ⟶ A)
    (hg : S.sheafificationMap ≫ g = f) :
    g = lift S f hf := sorry

/-- Morphisms from the sheafified localization agree when they agree after the
canonical map between sheafifications. -/
theorem hom_ext {A : Sheaf J CommRingCat.{max u v}}
    {f g : S.localizationSheaf ⟶ A}
    (h : S.sheafificationMap ≫ f = S.sheafificationMap ≫ g) :
    f = g := sorry

/-- A morphism from the sheafification of a ring presheaf which inverts the chosen sections
factors uniquely through the sheafified localization. -/
@[stacks 01D0 "universal property after sheafification"]
theorem existsUnique_lift {A : Sheaf J CommRingCat.{max u v}}
    (f : (presheafToSheaf J CommRingCat).obj O ⟶ A) (hf : Inverts S f) :
    ∃! g : S.localizationSheaf ⟶ A,
      S.sheafificationMap ≫ g = f := sorry

end Sheafification

end Presheaf

section Sheaf

variable {O : Sheaf J CommRingCat.{max u v}} (S : SubmonoidPresheaf O.obj)

/-- The canonical map from a sheaf of rings to its localization sheaf. -/
@[stacks 0EMC "map to localization sheaf"]
noncomputable def toLocalizationSheaf : O ⟶ S.localizationSheaf :=
  (sheafificationIso O).hom ≫
    S.sheafificationMap

/-- A morphism from the original sheaf inverts the chosen local sections. -/
@[stacks 0EMC "inverting distinguished local sections"]
def Inverts {A : Sheaf J CommRingCat.{max u v}} (f : O ⟶ A) : Prop :=
  S.MapsToUnits f.hom

/-- The canonical map to the localization sheaf inverts the chosen local sections. -/
theorem toLocalizationSheaf_inverts :
    S.Inverts S.toLocalizationSheaf := sorry

namespace LocalizationSheaf

/-- The presheaf-level lift underlying the universal map from a localization sheaf. -/
noncomputable def liftPresheaf {A : Sheaf J CommRingCat.{max u v}}
    (f : O ⟶ A) (hf : S.Inverts f) :
    S.localizationPresheaf ⟶ A.obj :=
  Universal.lift S f.hom hf

/-- The canonical map from the localization sheaf induced by a sheaf morphism which inverts
the chosen local sections. -/
noncomputable def lift {A : Sheaf J CommRingCat.{max u v}}
    (f : O ⟶ A) (hf : S.Inverts f) :
    S.localizationSheaf ⟶ A :=
  ⟨sheafifyLift J (liftPresheaf S f hf) A.property⟩

/-- The localization-sheaf lift factors the original morphism. -/
@[reassoc]
theorem lift_fac {A : Sheaf J CommRingCat.{max u v}}
    (f : O ⟶ A) (hf : S.Inverts f) :
    S.toLocalizationSheaf ≫ lift S f hf = f := sorry

/-- A morphism from the localization sheaf with the prescribed composite is the canonical
lift. -/
theorem lift_unique {A : Sheaf J CommRingCat.{max u v}}
    (f : O ⟶ A) (hf : S.Inverts f)
    (g : S.localizationSheaf ⟶ A)
    (hg : S.toLocalizationSheaf ≫ g = f) :
    g = lift S f hf := sorry

/-- Morphisms from the localization sheaf agree when they agree after the canonical map. -/
theorem hom_ext {A : Sheaf J CommRingCat.{max u v}}
    {f g : S.localizationSheaf ⟶ A}
    (h : S.toLocalizationSheaf ≫ f = S.toLocalizationSheaf ≫ g) :
    f = g := sorry

/-- A map of sheaves of rings which inverts the chosen local sections factors uniquely through
the localization sheaf. -/
@[stacks 0EMC "universal property of localization sheaf"]
theorem existsUnique_lift {A : Sheaf J CommRingCat.{max u v}}
    (f : O ⟶ A) (hf : S.Inverts f) :
    ∃! g : S.localizationSheaf ⟶ A,
      S.toLocalizationSheaf ≫ g = f := sorry

end LocalizationSheaf

end Sheaf

end CategoryTheory.Presheaf.SubmonoidPresheaf
