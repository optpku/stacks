module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import ReasLib.Algebra.Category.ModuleCat.ExteriorAlgebra.RestrictScalars
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing

/-!
# Exterior algebras of module presheaves

For a presheaf of commutative rings `𝒪`, this file constructs the sectionwise exterior-algebra
presheaf of a module presheaf over the underlying ring presheaf.  Restriction maps use the
bundled scalar-restriction owner, so no sectionwise scalar instance is installed by the caller.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace PresheafOfModules.ExteriorAlgebra

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})

/-- The underlying ring-valued presheaf of the commutative ring presheaf `𝒪`. -/
abbrev RingPresheaf := CategoryTheory.Presheaf.ringPresheafOfComm 𝒪

/-- A section module, viewed over the corresponding commutative section ring. -/
abbrev sectionObj (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    ModuleCat (𝒪.obj U) :=
  F.obj U

/-- A module-presheaf restriction map, viewed along the corresponding commutative ring map. -/
abbrev restriction (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    sectionObj 𝒪 F U ⟶
      (ModuleCat.restrictScalars (𝒪.map i).hom).obj (sectionObj 𝒪 F V) :=
  F.map i

/-- The exterior algebra of the module of sections over one object of the site. -/
abbrev obj (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    ModuleCat (𝒪.obj U) :=
  (sectionObj 𝒪 F U).exteriorAlgebra

/-- The restriction morphism on sectionwise exterior algebras. -/
noncomputable def map (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    obj 𝒪 F U ⟶
      (ModuleCat.restrictScalars (𝒪.map i).hom).obj (obj 𝒪 F V) :=
  ModuleCat.exteriorAlgebra.mapRestrictScalars (𝒪.map i).hom (restriction 𝒪 F i)

/-- The exterior-algebra restriction morphism sends a degree-one generator to the generator of
the restricted section. -/
@[simp]
theorem map_ι (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) (x : sectionObj 𝒪 F U) :
    map 𝒪 F i (ModuleCat.exteriorAlgebra.ι (sectionObj 𝒪 F U) x) =
      ModuleCat.exteriorAlgebra.ι (sectionObj 𝒪 F V) (restriction 𝒪 F i x) := sorry

/-- The sectionwise exterior-algebra restriction morphism preserves identity morphisms. -/
theorem map_id (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    map 𝒪 F (𝟙 U) =
      (ModuleCat.restrictScalarsId' (𝒪.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (𝒪.map_id U))).inv.app (obj 𝒪 F U) := sorry

/-- The sectionwise exterior-algebra restriction morphism preserves composition. -/
theorem map_comp (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪))
    {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    map 𝒪 F (i ≫ j) =
      map 𝒪 F i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map (map 𝒪 F j) ≫
        (ModuleCat.restrictScalarsComp' (𝒪.map i).hom (𝒪.map j).hom
          (𝒪.map (i ≫ j)).hom (congrArg CommRingCat.Hom.hom (𝒪.map_comp i j))).inv.app
          (obj 𝒪 F W) := sorry

set_option maxHeartbeats 800000 in
/-- The sectionwise exterior-algebra presheaf of `F`. -/
noncomputable def presheaf (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) :
    PresheafOfModules.{max w z} (RingPresheaf 𝒪) where
  obj U := obj 𝒪 F U
  map i := map 𝒪 F i
  map_id U := map_id 𝒪 F U
  map_comp i j := map_comp 𝒪 F i j

/-- Naturality of the sectionwise degree-one inclusions with respect to restriction maps. -/
theorem ι_app_naturality (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    restriction 𝒪 F i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map
          (ModuleCat.exteriorAlgebra.ιHom (sectionObj 𝒪 F V)) =
      ModuleCat.exteriorAlgebra.ιHom (sectionObj 𝒪 F U) ≫ map 𝒪 F i := sorry

/-- The degree-one inclusions assemble into a morphism to the exterior-algebra presheaf. -/
noncomputable def ι (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) :
    F ⟶ presheaf 𝒪 F where
  app U := ModuleCat.exteriorAlgebra.ιHom (sectionObj 𝒪 F U)
  naturality i := ι_app_naturality 𝒪 F i

/-- A component of the presheaf degree-one inclusion is the exterior-algebra inclusion. -/
theorem ι_app (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) (U : Cᵒᵖ) :
    (ι 𝒪 F).app U =
      ModuleCat.exteriorAlgebra.ιHom (sectionObj 𝒪 F U) := sorry

/-- A component of a module-presheaf morphism, viewed over the commutative section ring. -/
abbrev homApp {F G : PresheafOfModules.{max w z} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (U : Cᵒᵖ) : sectionObj 𝒪 F U ⟶ sectionObj 𝒪 G U :=
  f.app U

/-- Naturality of sectionwise exterior-algebra maps induced by a morphism of module presheaves. -/
theorem hom_naturality {F G : PresheafOfModules.{max w z} (RingPresheaf 𝒪)}
    (f : F ⟶ G) {U V : Cᵒᵖ} (i : U ⟶ V) :
    map 𝒪 F i ≫
        (ModuleCat.restrictScalars (𝒪.map i).hom).map
          (ModuleCat.exteriorAlgebra.map (homApp 𝒪 f V)) =
      ModuleCat.exteriorAlgebra.map (homApp 𝒪 f U) ≫ map 𝒪 G i := sorry

/-- The morphism on sectionwise exterior-algebra presheaves induced by a module-presheaf
morphism. -/
noncomputable def hom {F G : PresheafOfModules.{max w z} (RingPresheaf 𝒪)}
    (f : F ⟶ G) : presheaf 𝒪 F ⟶ presheaf 𝒪 G where
  app U := ModuleCat.exteriorAlgebra.map (homApp 𝒪 f U)
  naturality i := hom_naturality 𝒪 f i

/-- The induced morphism of exterior-algebra presheaves acts functorially on degree-one
generators. -/
@[simp]
theorem hom_app_ι {F G : PresheafOfModules.{max w z} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (U : Cᵒᵖ) (x : sectionObj 𝒪 F U) :
    (hom 𝒪 f).app U (ModuleCat.exteriorAlgebra.ι (sectionObj 𝒪 F U) x) =
      ModuleCat.exteriorAlgebra.ι (sectionObj 𝒪 G U) (homApp 𝒪 f U x) := sorry

/-- The exterior-algebra construction sends an identity morphism to an identity morphism. -/
theorem hom_id (F : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) :
    hom 𝒪 (𝟙 F) = 𝟙 (presheaf 𝒪 F) := sorry

/-- The exterior-algebra construction preserves composition of module-presheaf morphisms. -/
theorem hom_comp {F G H : PresheafOfModules.{max w z} (RingPresheaf 𝒪)}
    (f : F ⟶ G) (g : G ⟶ H) :
    hom 𝒪 (f ≫ g) = hom 𝒪 f ≫ hom 𝒪 g := sorry

/-- The sectionwise exterior-algebra endofunctor on module presheaves. -/
noncomputable def functor :
    PresheafOfModules.{max w z} (RingPresheaf 𝒪) ⥤
      PresheafOfModules.{max w z} (RingPresheaf 𝒪) where
  obj F := presheaf 𝒪 F
  map f := hom 𝒪 f
  map_id F := hom_id 𝒪 F
  map_comp f g := hom_comp 𝒪 f g

/-- The degree-one inclusions are natural in the module presheaf. -/
theorem ι_naturality {F G : PresheafOfModules.{max w z} (RingPresheaf 𝒪)} (f : F ⟶ G) :
    f ≫ ι 𝒪 G = ι 𝒪 F ≫ hom 𝒪 f := sorry

/-- The degree-one inclusions satisfy the naturality equation in functorial form. -/
theorem unit_naturality (F G : PresheafOfModules.{max w z} (RingPresheaf 𝒪)) (f : F ⟶ G) :
    (𝟭 _ : PresheafOfModules.{max w z} (RingPresheaf 𝒪) ⥤
        PresheafOfModules.{max w z} (RingPresheaf 𝒪)).map f ≫ ι 𝒪 G =
      ι 𝒪 F ≫ (functor 𝒪).map f := sorry

/-- The canonical degree-one inclusion into the sectionwise exterior-algebra functor. -/
noncomputable def unit :
    (𝟭 _ : PresheafOfModules.{max w z} (RingPresheaf 𝒪) ⥤
      PresheafOfModules.{max w z} (RingPresheaf 𝒪)) ⟶ functor 𝒪 where
  app F := ι 𝒪 F
  naturality := fun {F G} f ↦ unit_naturality 𝒪 F G f

end PresheafOfModules.ExteriorAlgebra
