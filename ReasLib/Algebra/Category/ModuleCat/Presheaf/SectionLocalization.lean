module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import ReasLib.Algebra.Category.Ring.Presheaf.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of module presheaves

A compatible submonoid family in a commutative-ring presheaf determines a change-of-rings
functor on module presheaves.  The change-of-rings adjunction is the canonical owner of
localization; the sectionwise `IsLocalizedModule` predicate records that its values have the
expected objectwise mathematical meaning.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf

noncomputable section

universe u v w z

namespace PresheafOfModules.SectionLocalization

variable {C : Type u} [Category.{v} C]
variable {O : Cᵒᵖ ⥤ CommRingCat.{w}}
variable (S : SubmonoidPresheaf O)

/-- The morphism of underlying ring presheaves induced by the canonical localization map. -/
@[stacks 01D1 "localized coefficient presheaf map"]
noncomputable abbrev structureMap :
    ringPresheafOfComm O ⟶ ringPresheafOfComm S.localizationPresheaf :=
  ringPresheafOfCommMap S.toLocalizationPresheaf

variable [(PresheafOfModules.pushforward.{z}
  (PresheafOfModules.ChangeOfRings.homOverId (structureMap S))).IsRightAdjoint]

/-- Lemma 17.27.2 (01D1) (1): localization of module presheaves is extension of
scalars along the localization of the coefficient presheaf. -/
@[stacks 01D1 "localization functor for module presheaves"]
noncomputable def functor :
    PresheafOfModules.{z} (ringPresheafOfComm O) ⥤
      PresheafOfModules.{z} (ringPresheafOfComm S.localizationPresheaf) :=
  PresheafOfModules.ChangeOfRings.extension (structureMap S)

/-- The localized module presheaf associated to a module presheaf over the original
coefficient presheaf. -/
noncomputable abbrev obj
    (F : PresheafOfModules.{z} (ringPresheafOfComm O)) :
    PresheafOfModules.{z} (ringPresheafOfComm S.localizationPresheaf) :=
  (functor S).obj F

/-- Localization of module presheaves is left adjoint to restriction of scalars. -/
noncomputable def adjunction :
    functor S ⊣ PresheafOfModules.restrictScalars.{z} (structureMap S) :=
  PresheafOfModules.ChangeOfRings.extensionRestrictionAdjunction (structureMap S)

/-- The canonical map from a module presheaf to the restriction of its localization. -/
noncomputable def unit
    (F : PresheafOfModules.{z} (ringPresheafOfComm O)) :
    F ⟶ (PresheafOfModules.restrictScalars.{z} (structureMap S)).obj (obj S F) :=
  (adjunction S).unit.app F

/-- A morphism into a module presheaf over the localized coefficients exhibits a
sectionwise localization when every component is an `IsLocalizedModule` map. -/
@[stacks 01D1 "sectionwise localization predicate"]
def IsSectionwiseLocalization
    {F : PresheafOfModules.{z} (ringPresheafOfComm O)}
    {G : PresheafOfModules.{z} (ringPresheafOfComm S.localizationPresheaf)}
    (f : F ⟶ (PresheafOfModules.restrictScalars.{z} (structureMap S)).obj G) : Prop :=
  ∀ U, IsLocalizedModule (S.obj U) (f.app U).hom

/-- Lemma 17.27.2 (01D1) (1): the unit of module-presheaf localization is
sectionwise the usual localization map `F(U) ⟶ S(U)⁻¹F(U)`. -/
@[stacks 01D1 "sectionwise localized-module specification"]
theorem unit_isSectionwiseLocalization
    (F : PresheafOfModules.{z} (ringPresheafOfComm O)) :
    IsSectionwiseLocalization S (unit S F) := sorry

/-- The component of the localization unit is a canonical `IsLocalizedModule` map;
this instance makes the sectionwise specification directly reusable. -/
noncomputable instance unitAppIsLocalizedModule
    (F : PresheafOfModules.{z} (ringPresheafOfComm O)) (U : Cᵒᵖ) :
    IsLocalizedModule (S.obj U) ((unit S F).app U).hom := sorry

/-- The Hom equivalence characterizing localization of module presheaves. -/
noncomputable def homEquiv
    (F : PresheafOfModules.{z} (ringPresheafOfComm O))
    (G : PresheafOfModules.{z} (ringPresheafOfComm S.localizationPresheaf)) :
    (obj S F ⟶ G) ≃
      (F ⟶ (PresheafOfModules.restrictScalars.{z} (structureMap S)).obj G) :=
  (adjunction S).homEquiv F G

/-- The adjoint transpose of a morphism into a restricted module presheaf. -/
noncomputable def lift
    {F : PresheafOfModules.{z} (ringPresheafOfComm O)}
    {G : PresheafOfModules.{z} (ringPresheafOfComm S.localizationPresheaf)}
    (f : F ⟶ (PresheafOfModules.restrictScalars.{z} (structureMap S)).obj G) :
    obj S F ⟶ G :=
  (homEquiv S F G).symm f

/-- The localization lift factors the original morphism through the unit. -/
@[reassoc]
theorem lift_fac
    {F : PresheafOfModules.{z} (ringPresheafOfComm O)}
    {G : PresheafOfModules.{z} (ringPresheafOfComm S.localizationPresheaf)}
    (f : F ⟶ (PresheafOfModules.restrictScalars.{z} (structureMap S)).obj G) :
    unit S F ≫ (PresheafOfModules.restrictScalars.{z} (structureMap S)).map (lift S f) = f := sorry

/-- A map from a localized module presheaf with the prescribed restriction is the
canonical adjoint transpose. -/
theorem lift_unique
    {F : PresheafOfModules.{z} (ringPresheafOfComm O)}
    {G : PresheafOfModules.{z} (ringPresheafOfComm S.localizationPresheaf)}
    (f : F ⟶ (PresheafOfModules.restrictScalars.{z} (structureMap S)).obj G)
    (g : obj S F ⟶ G)
    (hg : unit S F ≫
      (PresheafOfModules.restrictScalars.{z} (structureMap S)).map g = f) :
    g = lift S f := sorry

/-- Morphisms from a localized module presheaf agree when their restrictions agree after the
localization unit. -/
@[stacks 01D1 "extensionality for localized module presheaves"]
theorem hom_ext
    {F : PresheafOfModules.{z} (ringPresheafOfComm O)}
    {G : PresheafOfModules.{z} (ringPresheafOfComm S.localizationPresheaf)}
    {f g : obj S F ⟶ G}
    (h : unit S F ≫ (PresheafOfModules.restrictScalars.{z} (structureMap S)).map f =
      unit S F ≫ (PresheafOfModules.restrictScalars.{z} (structureMap S)).map g) :
    f = g := sorry

/-- The universal property of localization for module presheaves. -/
@[stacks 01D1 "universal property of localized module presheaves"]
theorem existsUnique_lift
    {F : PresheafOfModules.{z} (ringPresheafOfComm O)}
    {G : PresheafOfModules.{z} (ringPresheafOfComm S.localizationPresheaf)}
    (f : F ⟶ (PresheafOfModules.restrictScalars.{z} (structureMap S)).obj G) :
    ∃! g : obj S F ⟶ G,
      unit S F ≫ (PresheafOfModules.restrictScalars.{z} (structureMap S)).map g = f := sorry

-- The functorial data come from the canonical change-of-rings adjunction. Any inherited
-- `sorryAx` in them comes from functor-law or naturality proof fields of the localization map;
-- the new `IsLocalizedModule` proof debt is Prop-valued and supplies no carrier or map.

end PresheafOfModules.SectionLocalization
