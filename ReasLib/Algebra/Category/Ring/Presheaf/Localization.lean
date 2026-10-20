module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Localization.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of commutative-ring presheaves

This file extends the localization API for presheaves on topological spaces to presheaves on an
arbitrary category.  A compatible family of submonoids determines an explicit objectwise
localization functor, its canonical map, and the maps supplied by the localization universal
property.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]

/-- A compatible family of submonoids in a commutative-ring-valued presheaf. -/
@[stacks 0EMB "compatible submonoid family"]
abbrev SubmonoidPresheaf (O : Cᵒᵖ ⥤ CommRingCat.{w}) :=
  { family : ∀ U : Cᵒᵖ, Submonoid (O.obj U) //
      ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V), family U ≤ (family V).comap (O.map f).hom }

namespace SubmonoidPresheaf

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}} (S : SubmonoidPresheaf O)

/-- The submonoid of sections at an object. -/
abbrev obj (U : Cᵒᵖ) : Submonoid (O.obj U) := S.1 U

/-- Restriction maps preserve the chosen submonoids. -/
abbrev map {U V : Cᵒᵖ} (f : U ⟶ V) : S.obj U ≤ (S.obj V).comap (O.map f).hom := S.2 f

/-- Construct a compatible family from its objectwise submonoids and restriction proof. -/
def mk (family : ∀ U : Cᵒᵖ, Submonoid (O.obj U))
    (compatibility : ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V), family U ≤ (family V).comap (O.map f).hom) :
    SubmonoidPresheaf O := ⟨family, compatibility⟩

/-- The localization of the ring of sections at one object. -/
noncomputable abbrev localizationObj (U : Cᵒᵖ) : CommRingCat.{w} :=
  CommRingCat.of (Localization (S.obj U))

/-- Restriction on objectwise localizations, induced by restriction on the original presheaf. -/
noncomputable def localizationMap {U V : Cᵒᵖ} (f : U ⟶ V) :
    S.localizationObj U ⟶ S.localizationObj V :=
  CommRingCat.ofHom (IsLocalization.map _ (O.map f).hom (S.map f))

/-- Objectwise localization respects identity restriction maps. -/
theorem localizationMap_id (U : Cᵒᵖ) :
    S.localizationMap (𝟙 U) = 𝟙 (S.localizationObj U) := sorry

/-- Objectwise localization respects composition of restriction maps. -/
theorem localizationMap_comp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    S.localizationMap (f ≫ g) = S.localizationMap f ≫ S.localizationMap g := sorry

/-- The objectwise localization presheaf associated to a compatible family of submonoids. -/
@[stacks 0EMB "localization presheaf"]
protected noncomputable def localizationPresheaf : Cᵒᵖ ⥤ CommRingCat.{w} where
  obj := S.localizationObj
  map := S.localizationMap
  map_id := S.localizationMap_id
  map_comp := S.localizationMap_comp

/-- Each value of the localization presheaf carries its canonical algebra structure over the
original ring of sections. -/
noncomputable instance localizationAlgebra (U : Cᵒᵖ) :
    Algebra (O.obj U) (S.localizationPresheaf.obj U) :=
  inferInstanceAs (Algebra (O.obj U) (Localization (S.obj U)))

/-- Each value of the localization presheaf satisfies the canonical `IsLocalization`
property. -/
noncomputable instance localizationIsLocalization (U : Cᵒᵖ) :
    IsLocalization (S.obj U) (S.localizationPresheaf.obj U) :=
  inferInstanceAs (IsLocalization (S.obj U) (Localization (S.obj U)))

/-- The component of the canonical map from a presheaf to its objectwise localization. -/
noncomputable def toLocalizationPresheafApp (U : Cᵒᵖ) :
    O.obj U ⟶ S.localizationPresheaf.obj U :=
  CommRingCat.ofHom (algebraMap (O.obj U) (Localization (S.obj U)))

/-- The components of the canonical localization map commute with restriction. -/
theorem toLocalizationPresheafApp_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    O.map f ≫ S.toLocalizationPresheafApp V =
      S.toLocalizationPresheafApp U ≫ S.localizationPresheaf.map f := sorry

/-- The canonical morphism from a presheaf of rings to its objectwise localization. -/
@[stacks 0EMB "map to localization presheaf"]
noncomputable def toLocalizationPresheaf : O ⟶ S.localizationPresheaf where
  app := S.toLocalizationPresheafApp
  naturality _ _ f := S.toLocalizationPresheafApp_naturality f

/-- A morphism out of the original presheaf maps the distinguished sections to units. -/
@[stacks 01D0 "maps distinguished sections to units",
  stacks 0EMB "maps distinguished sections to units"]
def MapsToUnits {A : Cᵒᵖ ⥤ CommRingCat.{w}} (f : O ⟶ A) : Prop :=
  ∀ ⦃U : Cᵒᵖ⦄ (s : S.obj U), IsUnit ((f.app U).hom s.1)

/-- The canonical localization morphism maps every distinguished section to a unit. -/
@[stacks 01D0 "distinguished sections become units"]
theorem toLocalizationPresheaf_mapsToUnits :
    S.MapsToUnits S.toLocalizationPresheaf := sorry

namespace Universal

/-- The component of the lift through a localization presheaf. -/
noncomputable def liftApp {A : Cᵒᵖ ⥤ CommRingCat.{w}}
    (f : O ⟶ A) (hf : S.MapsToUnits f) (U : Cᵒᵖ) :
    S.localizationPresheaf.obj U ⟶ A.obj U :=
  CommRingCat.ofHom (IsLocalization.lift (fun s ↦ hf s))

/-- The objectwise localization lifts commute with restriction maps. -/
theorem liftApp_naturality {A : Cᵒᵖ ⥤ CommRingCat.{w}}
    (f : O ⟶ A) (hf : S.MapsToUnits f) {U V : Cᵒᵖ} (g : U ⟶ V) :
    S.localizationPresheaf.map g ≫ liftApp S f hf V =
      liftApp S f hf U ≫ A.map g := sorry

/-- The explicit morphism from the localization presheaf induced by a map which sends the
distinguished sections to units. -/
noncomputable def lift {A : Cᵒᵖ ⥤ CommRingCat.{w}}
    (f : O ⟶ A) (hf : S.MapsToUnits f) :
    S.localizationPresheaf ⟶ A where
  app := liftApp S f hf
  naturality _ _ g := liftApp_naturality S f hf g

/-- The localization lift factors the original morphism. -/
@[reassoc]
theorem lift_fac {A : Cᵒᵖ ⥤ CommRingCat.{w}}
    (f : O ⟶ A) (hf : S.MapsToUnits f) :
    S.toLocalizationPresheaf ≫ lift S f hf = f := sorry

/-- A morphism out of the localization presheaf with the prescribed composite is the canonical
lift. -/
theorem lift_unique {A : Cᵒᵖ ⥤ CommRingCat.{w}}
    (f : O ⟶ A) (hf : S.MapsToUnits f)
    (g : S.localizationPresheaf ⟶ A)
    (hg : S.toLocalizationPresheaf ≫ g = f) :
    g = lift S f hf := sorry

/-- Morphisms from a localization presheaf are equal when they agree after the canonical map. -/
theorem hom_ext {A : Cᵒᵖ ⥤ CommRingCat.{w}}
    {f g : S.localizationPresheaf ⟶ A}
    (h : S.toLocalizationPresheaf ≫ f = S.toLocalizationPresheaf ≫ g) :
    f = g := sorry

/-- The universal property of the objectwise localization presheaf. -/
@[stacks 01D0 "universal property of a localization presheaf"]
theorem existsUnique_lift {A : Cᵒᵖ ⥤ CommRingCat.{w}}
    (f : O ⟶ A) (hf : S.MapsToUnits f) :
    ∃! g : S.localizationPresheaf ⟶ A,
      S.toLocalizationPresheaf ≫ g = f := sorry

end Universal

end SubmonoidPresheaf

end CategoryTheory.Presheaf
