module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import ReasLib.Algebra.Category.ModuleCat.SymmetricAlgebra.RestrictScalars

/-!
# Symmetric algebras of module presheaves

For a presheaf of commutative rings `𝒪`, this file constructs the sectionwise symmetric-algebra
presheaf of a presheaf of modules over the underlying ring presheaf.  Restriction maps are built
from the bundled scalar-restriction API, so no ambient module or algebra instance is replaced.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace PresheafOfModules.SymmetricAlgebra

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})

/-- The underlying ring-valued presheaf of the commutative ring presheaf `𝒪`. -/
abbrev RingPresheaf := CategoryTheory.Presheaf.ringPresheafOfComm 𝒪

/-- A section module, viewed over its commutative section ring. -/
abbrev sectionObj (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    ModuleCat (𝒪.obj U) :=
  F.obj U

/-- A module-presheaf restriction map, viewed along the corresponding commutative ring map. -/
abbrev restriction (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    sectionObj 𝒪 F U ⟶
      (ModuleCat.restrictScalars (𝒪.map i).hom).obj (sectionObj 𝒪 F V) :=
  F.map i

/-- The symmetric algebra of the module of sections over one object of the site. -/
abbrev obj (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    ModuleCat (𝒪.obj U) :=
  (sectionObj 𝒪 F U).symmetricAlgebra

/-- The multiplicative restriction map on sectionwise symmetric algebras. -/
noncomputable abbrev restrictionRingHom
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) {U V : Cᵒᵖ} (i : U ⟶ V) :
    _root_.SymmetricAlgebra (𝒪.obj U) (sectionObj 𝒪 F U) →+*
      _root_.SymmetricAlgebra (𝒪.obj V) (sectionObj 𝒪 F V) :=
  ModuleCat.symmetricAlgebra.mapRestrictScalarsRingHom
    (𝒪.map i).hom (restriction 𝒪 F i)

/-- The restriction morphism on sectionwise symmetric algebras. -/
noncomputable def map (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    obj 𝒪 F U ⟶
      (ModuleCat.restrictScalars (𝒪.map i).hom).obj (obj 𝒪 F V) :=
  ModuleCat.symmetricAlgebra.mapRestrictScalars (𝒪.map i).hom (restriction 𝒪 F i)

/-- The sectionwise restriction morphism acts on symmetric-algebra generators by restricting
their underlying sections. -/
@[simp]
theorem map_ι (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) (x : sectionObj 𝒪 F U) :
    map 𝒪 F i (ModuleCat.symmetricAlgebra.ι (sectionObj 𝒪 F U) x) =
      ModuleCat.symmetricAlgebra.ι (sectionObj 𝒪 F V) (restriction 𝒪 F i x) := sorry

/-- The sectionwise symmetric-algebra restriction morphism preserves identity morphisms. -/
theorem map_id (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    map 𝒪 F (𝟙 U) =
      (ModuleCat.restrictScalarsId' (𝒪.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (𝒪.map_id U))).inv.app (obj 𝒪 F U) := sorry

/-- The sectionwise symmetric-algebra restriction morphism preserves composition. -/
theorem map_comp (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    map 𝒪 F (i ≫ j) =
      map 𝒪 F i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map (map 𝒪 F j) ≫
        (ModuleCat.restrictScalarsComp' (𝒪.map i).hom (𝒪.map j).hom
          (𝒪.map (i ≫ j)).hom (congrArg CommRingCat.Hom.hom (𝒪.map_comp i j))).inv.app
          (obj 𝒪 F W) := sorry

/-- The sectionwise symmetric-algebra presheaf of `F`. -/
noncomputable def presheaf (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    PresheafOfModules.{w} (RingPresheaf 𝒪) where
  obj := obj 𝒪 F
  map := map 𝒪 F
  map_id := map_id 𝒪 F
  map_comp := map_comp 𝒪 F

/-- The sectionwise degree-one inclusions commute with restriction morphisms. -/
theorem ι_naturality_obj (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    restriction 𝒪 F i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map
          (ModuleCat.symmetricAlgebra.ιHom (sectionObj 𝒪 F V)) =
      ModuleCat.symmetricAlgebra.ιHom (sectionObj 𝒪 F U) ≫ map 𝒪 F i := sorry

/-- The degree-one inclusions assemble into a morphism to the symmetric-algebra presheaf. -/
noncomputable def ι (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    F ⟶ presheaf 𝒪 F where
  app U := ModuleCat.symmetricAlgebra.ιHom (sectionObj 𝒪 F U)
  naturality := ι_naturality_obj 𝒪 F

/-- A component of the presheaf degree-one inclusion is the symmetric-algebra inclusion. -/
theorem ι_app (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    (ι 𝒪 F).app U =
      ModuleCat.symmetricAlgebra.ιHom (sectionObj 𝒪 F U) := sorry

/-- A component of a module-presheaf morphism over the commutative section ring. -/
abbrev homApp {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (U : Cᵒᵖ) : sectionObj 𝒪 F U ⟶ sectionObj 𝒪 G U :=
  f.app U

/-- Naturality of the sectionwise symmetric-algebra maps induced by a morphism of module
presheaves. -/
theorem hom_naturality {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)}
    (f : F ⟶ G) {U V : Cᵒᵖ} (i : U ⟶ V) :
    map 𝒪 F i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map
          (ModuleCat.symmetricAlgebra.map (homApp 𝒪 f V)) =
      ModuleCat.symmetricAlgebra.map (homApp 𝒪 f U) ≫ map 𝒪 G i := sorry

/-- The morphism on sectionwise symmetric-algebra presheaves induced by a morphism of module
presheaves. -/
noncomputable def hom {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)}
    (f : F ⟶ G) : presheaf 𝒪 F ⟶ presheaf 𝒪 G where
  app U := ModuleCat.symmetricAlgebra.map (homApp 𝒪 f U)
  naturality := hom_naturality 𝒪 f

/-- The induced morphism of symmetric-algebra presheaves agrees with the original morphism on
generators. -/
@[simp]
theorem hom_app_ι {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (U : Cᵒᵖ) (x : sectionObj 𝒪 F U) :
    (hom 𝒪 f).app U (ModuleCat.symmetricAlgebra.ι (sectionObj 𝒪 F U) x) =
      ModuleCat.symmetricAlgebra.ι (sectionObj 𝒪 G U) (homApp 𝒪 f U x) := sorry

/-- The symmetric-algebra construction sends an identity morphism to an identity morphism. -/
theorem hom_id (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    hom 𝒪 (𝟙 F) = 𝟙 (presheaf 𝒪 F) := sorry

/-- The symmetric-algebra construction preserves composition of module-presheaf morphisms. -/
theorem hom_comp {F G H : PresheafOfModules.{w} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (g : G ⟶ H) :
    hom 𝒪 (f ≫ g) = hom 𝒪 f ≫ hom 𝒪 g := sorry

/-- The sectionwise symmetric-algebra endofunctor on module presheaves. -/
noncomputable def functor :
    PresheafOfModules.{w} (RingPresheaf 𝒪) ⥤
      PresheafOfModules.{w} (RingPresheaf 𝒪) where
  obj := presheaf 𝒪
  map := hom 𝒪
  map_id := hom_id 𝒪
  map_comp := hom_comp 𝒪

/-- The degree-one inclusions are natural in the module presheaf. -/
theorem ι_naturality {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)} (f : F ⟶ G) :
    f ≫ ι 𝒪 G = ι 𝒪 F ≫ hom 𝒪 f := sorry

/-- The degree-one inclusions satisfy the naturality equation in functorial form. -/
theorem unit_naturality (F G : PresheafOfModules.{w} (RingPresheaf 𝒪)) (f : F ⟶ G) :
    (𝟭 _ : PresheafOfModules.{w} (RingPresheaf 𝒪) ⥤
        PresheafOfModules.{w} (RingPresheaf 𝒪)).map f ≫ ι 𝒪 G =
      ι 𝒪 F ≫ (functor 𝒪).map f := sorry

/-- The canonical degree-one inclusion into the sectionwise symmetric-algebra functor. -/
noncomputable def unit :
    (𝟭 _ : PresheafOfModules.{w} (RingPresheaf 𝒪) ⥤
      PresheafOfModules.{w} (RingPresheaf 𝒪)) ⟶ functor 𝒪 where
  app F := ι 𝒪 F
  naturality := fun {F G} f ↦ unit_naturality 𝒪 F G f

end PresheafOfModules.SymmetricAlgebra
