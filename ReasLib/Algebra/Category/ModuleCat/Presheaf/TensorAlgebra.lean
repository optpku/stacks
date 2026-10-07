module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import ReasLib.Algebra.Category.ModuleCat.TensorAlgebra.RestrictScalars

/-!
# Tensor algebras of module presheaves

For a presheaf of commutative rings `𝒪`, this file constructs the sectionwise tensor-algebra
presheaf of a module presheaf over the underlying ring presheaf.  Restriction maps are induced by
the bundled scalar-restriction API, and the degree-one inclusions form a natural transformation.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace PresheafOfModules.TensorAlgebra

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})

/-- The underlying ring-valued presheaf of the commutative ring presheaf `𝒪`. -/
abbrev RingPresheaf := CategoryTheory.Presheaf.ringPresheafOfComm 𝒪

/-- A section module, viewed over its commutative section ring. -/
abbrev sectionObj (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    ModuleCat (𝒪.obj U) :=
  F.obj U

/-- A module-presheaf restriction map, bundled as a morphism into restriction of scalars. -/
abbrev restriction (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    sectionObj 𝒪 F U ⟶
      (ModuleCat.restrictScalars (𝒪.map i).hom).obj (sectionObj 𝒪 F V) :=
  F.map i

/-- The tensor algebra of the module of sections over one object of the site. -/
abbrev obj (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    ModuleCat (𝒪.obj U) :=
  (sectionObj 𝒪 F U).tensorAlgebra

/-- The multiplicative restriction map on sectionwise tensor algebras. -/
noncomputable abbrev restrictionRingHom
    (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) {U V : Cᵒᵖ} (i : U ⟶ V) :
    TensorAlgebra (𝒪.obj U) (sectionObj 𝒪 F U) →+*
      TensorAlgebra (𝒪.obj V) (sectionObj 𝒪 F V) :=
  ModuleCat.tensorAlgebra.mapRestrictScalarsRingHom
    (𝒪.map i).hom (restriction 𝒪 F i)

/-- The bundled restriction morphism on sectionwise tensor algebras. -/
noncomputable def map (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    obj 𝒪 F U ⟶ (ModuleCat.restrictScalars (𝒪.map i).hom).obj (obj 𝒪 F V) :=
  ModuleCat.tensorAlgebra.mapRestrictScalars (𝒪.map i).hom (restriction 𝒪 F i)

/-- The multiplicative restriction map sends a degree-one generator to the restricted section. -/
@[simp]
theorem restrictionRingHom_ι (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) (m : sectionObj 𝒪 F U) :
    restrictionRingHom 𝒪 F i (TensorAlgebra.ι (𝒪.obj U) m) =
      TensorAlgebra.ι (𝒪.obj V) (restriction 𝒪 F i m) := sorry

/-- A sectionwise tensor-algebra restriction map sends a degree-one generator to the restricted
section. -/
@[simp]
theorem map_ι (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) (m : sectionObj 𝒪 F U) :
    map 𝒪 F i (ModuleCat.tensorAlgebra.ι (sectionObj 𝒪 F U) m) =
      ModuleCat.tensorAlgebra.ι (sectionObj 𝒪 F V) (restriction 𝒪 F i m) := sorry

/-- The sectionwise tensor-algebra restriction morphism preserves identity morphisms. -/
theorem map_id (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    map 𝒪 F (𝟙 U) =
      (ModuleCat.restrictScalarsId' (𝒪.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (𝒪.map_id U))).inv.app (obj 𝒪 F U) := sorry

/-- The sectionwise tensor-algebra restriction morphism preserves composition. -/
theorem map_comp (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    map 𝒪 F (i ≫ j) =
      map 𝒪 F i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map (map 𝒪 F j) ≫
        (ModuleCat.restrictScalarsComp' (𝒪.map i).hom (𝒪.map j).hom
          (𝒪.map (i ≫ j)).hom (congrArg CommRingCat.Hom.hom (𝒪.map_comp i j))).inv.app
          (obj 𝒪 F W) := sorry

/-- The sectionwise tensor-algebra presheaf of a module presheaf. -/
noncomputable def presheaf (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    PresheafOfModules.{w} (RingPresheaf 𝒪) where
  obj := obj 𝒪 F
  map := map 𝒪 F
  map_id := map_id 𝒪 F
  map_comp := map_comp 𝒪 F

/-- Naturality of the sectionwise degree-one inclusions with respect to restriction maps. -/
theorem ι_app_naturality (F : PresheafOfModules.{w} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    restriction 𝒪 F i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map
          (ModuleCat.tensorAlgebra.ιHom (sectionObj 𝒪 F V)) =
      ModuleCat.tensorAlgebra.ιHom (sectionObj 𝒪 F U) ≫ map 𝒪 F i := sorry

/-- The degree-one inclusions assemble into a morphism to the tensor-algebra presheaf. -/
noncomputable def ι (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    F ⟶ presheaf 𝒪 F where
  app U := ModuleCat.tensorAlgebra.ιHom (sectionObj 𝒪 F U)
  naturality := ι_app_naturality 𝒪 F

/-- A component of the presheaf degree-one inclusion is the bundled tensor-algebra inclusion. -/
theorem ι_app (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    (ι 𝒪 F).app U = ModuleCat.tensorAlgebra.ιHom (sectionObj 𝒪 F U) := sorry

/-- A component of a module-presheaf morphism over its commutative section ring. -/
abbrev homApp {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (U : Cᵒᵖ) : sectionObj 𝒪 F U ⟶ sectionObj 𝒪 G U :=
  f.app U

/-- Naturality of the sectionwise tensor-algebra maps induced by a module-presheaf morphism. -/
theorem hom_naturality {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)}
    (f : F ⟶ G) {U V : Cᵒᵖ} (i : U ⟶ V) :
    map 𝒪 F i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map
          (ModuleCat.tensorAlgebra.map (homApp 𝒪 f V)) =
      ModuleCat.tensorAlgebra.map (homApp 𝒪 f U) ≫ map 𝒪 G i := sorry

/-- The morphism on sectionwise tensor-algebra presheaves induced by a module-presheaf
morphism. -/
noncomputable def hom {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)}
    (f : F ⟶ G) : presheaf 𝒪 F ⟶ presheaf 𝒪 G where
  app U := ModuleCat.tensorAlgebra.map (homApp 𝒪 f U)
  naturality := hom_naturality 𝒪 f

/-- The induced presheaf morphism sends degree-one generators to image generators. -/
@[simp]
theorem hom_app_ι {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (U : Cᵒᵖ) (m : sectionObj 𝒪 F U) :
    (hom 𝒪 f).app U (ModuleCat.tensorAlgebra.ι (sectionObj 𝒪 F U) m) =
      ModuleCat.tensorAlgebra.ι (sectionObj 𝒪 G U) (homApp 𝒪 f U m) := sorry

/-- The tensor-algebra construction sends an identity presheaf morphism to an identity. -/
theorem hom_id (F : PresheafOfModules.{w} (RingPresheaf 𝒪)) :
    hom 𝒪 (𝟙 F) = 𝟙 (presheaf 𝒪 F) := sorry

/-- The tensor-algebra construction preserves composition of presheaf morphisms. -/
theorem hom_comp {F G H : PresheafOfModules.{w} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (g : G ⟶ H) :
    hom 𝒪 (f ≫ g) = hom 𝒪 f ≫ hom 𝒪 g := sorry

/-- The sectionwise tensor-algebra endofunctor on module presheaves. -/
noncomputable def functor :
    PresheafOfModules.{w} (RingPresheaf 𝒪) ⥤
      PresheafOfModules.{w} (RingPresheaf 𝒪) where
  obj F := presheaf 𝒪 F
  map f := hom 𝒪 f
  map_id F := hom_id 𝒪 F
  map_comp f g := hom_comp 𝒪 f g

/-- The degree-one inclusions are natural in the module presheaf. -/
theorem ι_naturality {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)} (f : F ⟶ G) :
    f ≫ ι 𝒪 G = ι 𝒪 F ≫ hom 𝒪 f := sorry

/-- The degree-one inclusions satisfy the naturality equation in functorial form. -/
theorem unit_naturality (F G : PresheafOfModules.{w} (RingPresheaf 𝒪)) (f : F ⟶ G) :
    (𝟭 _).map f ≫ ι 𝒪 G = ι 𝒪 F ≫ (functor 𝒪).map f := sorry

/-- The canonical degree-one inclusion into the sectionwise tensor-algebra functor. -/
noncomputable def unit : 𝟭 _ ⟶ functor 𝒪 where
  app F := ι 𝒪 F
  naturality := fun {F G} f ↦ unit_naturality 𝒪 F G f

end PresheafOfModules.TensorAlgebra
