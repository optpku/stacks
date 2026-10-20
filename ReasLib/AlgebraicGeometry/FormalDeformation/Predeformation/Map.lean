module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Category
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber

/-!
# Functoriality of predeformation categories

A morphism of categories fibred in groupoids induces a based functor between
the corresponding categories of residue lifts.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (toFunctor fiberFunctor)

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}

/-- The image of a chosen residue object under a morphism of categories fibred in groupoids. -/
def residueImage (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS)) :
    Y.p.Fiber (Over.mk kToS) :=
  (fiberFunctor F (Over.mk kToS)).obj x0

/-- The total object underlying the image of a residue object is the image under the total functor. -/
theorem residueImage_obj (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS)) :
    Functor.Fiber.fiberInclusion.obj (residueImage F x0) =
      (toFunctor F).obj (Functor.Fiber.fiberInclusion.obj x0) :=
  sorry

/-- The predeformation category associated to a residue object, viewed as a based category. -/
abbrev predeformation
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
    (x0 : X.p.Fiber (Over.mk kToS)) : BasedCategory (ArtinianLocalAlgCat Λ k) :=
  BasedCategory.ofFunctor (forget openImmersion kToS h_factor X x0)

/-- The projection of a predeformation category is its forgetful functor to Artinian local algebras. -/
theorem predeformation_p
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
    (x0 : X.p.Fiber (Over.mk kToS)) :
    (predeformation openImmersion h_factor X x0).p =
      forget openImmersion kToS h_factor X x0 :=
  sorry

/-- The residue arrow of the image of a predeformation object lies over the residue spectrum map. -/
theorem mapObj_over_fromResidue (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    (ξ : Obj openImmersion kToS h_factor X x0) :
    Y.p.IsHomLift (specOver_toResidue openImmersion kToS h_factor ξ.base)
      ((toFunctor F).map ξ.fromResidue) :=
  sorry

/-- The image of a predeformation object under a morphism of categories fibred in groupoids. -/
def mapObj (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    (ξ : Obj openImmersion kToS h_factor X x0) :
    Obj openImmersion kToS h_factor Y (residueImage F x0) where
  base := ξ.base
  target := (fiberFunctor F (specOver openImmersion ξ.base)).obj ξ.target
  fromResidue := (toFunctor F).map ξ.fromResidue
  over_fromResidue := mapObj_over_fromResidue openImmersion h_factor F x0 ξ

/-- The image of a reversed predeformation arrow lies over its underlying base map. -/
theorem mapHom_over_hom (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    {ξ η : Obj openImmersion kToS h_factor X x0} (f : Hom ξ η) :
    Y.p.IsHomLift (specOverMap openImmersion f.baseHom) ((toFunctor F).map f.hom) :=
  sorry

/-- The image of a reversed predeformation arrow satisfies the corresponding residue triangle. -/
theorem mapHom_triangle (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    {ξ η : Obj openImmersion kToS h_factor X x0} (f : Hom ξ η) :
    (toFunctor F).map ξ.fromResidue =
      (toFunctor F).map η.fromResidue ≫ (toFunctor F).map f.hom :=
  sorry

/-- The image of a reversed predeformation arrow under a morphism of categories fibred in groupoids. -/
def mapHom (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    {ξ η : Obj openImmersion kToS h_factor X x0} (f : Hom ξ η) :
    Hom (mapObj openImmersion h_factor F x0 ξ) (mapObj openImmersion h_factor F x0 η) where
  baseHom := f.baseHom
  hom := (toFunctor F).map f.hom
  over_hom := mapHom_over_hom openImmersion h_factor F x0 f
  triangle := mapHom_triangle openImmersion h_factor F x0 f

/-- The image of an identity predeformation arrow is the identity arrow. -/
theorem mapHom_id (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    (ξ : Obj openImmersion kToS h_factor X x0) :
    mapHom openImmersion h_factor F x0 (Hom.id ξ) =
      Hom.id (mapObj openImmersion h_factor F x0 ξ) :=
  sorry

/-- The image of a composite predeformation arrow is the composite of the images. -/
theorem mapHom_comp (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    {ξ η ζ : Obj openImmersion kToS h_factor X x0} (f : Hom ξ η) (g : Hom η ζ) :
    mapHom openImmersion h_factor F x0 (Hom.comp f g) =
      Hom.comp (mapHom openImmersion h_factor F x0 f)
        (mapHom openImmersion h_factor F x0 g) :=
  sorry

/-- The ordinary functor induced on predeformation categories by a morphism of fibred groupoids. -/
def mapFunctor (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS)) :
    (predeformation openImmersion h_factor X x0).obj ⥤
      (predeformation openImmersion h_factor Y (residueImage F x0)).obj where
  obj := mapObj openImmersion h_factor F x0
  map f := mapHom openImmersion h_factor F x0 f
  map_id := mapHom_id openImmersion h_factor F x0
  map_comp := mapHom_comp openImmersion h_factor F x0

/-- The induced ordinary functor preserves the Artinian local algebra projection. -/
theorem mapFunctor_forget (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS)) :
    mapFunctor openImmersion h_factor F x0 ⋙
        forget openImmersion kToS h_factor Y (residueImage F x0) =
      forget openImmersion kToS h_factor X x0 :=
  sorry

/-- A morphism of categories fibred in groupoids induces a based functor on predeformations. -/
def map (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS)) :
    predeformation openImmersion h_factor X x0 ⥤ᵇ
      predeformation openImmersion h_factor Y (residueImage F x0) where
  toFunctor := mapFunctor openImmersion h_factor F x0
  w := mapFunctor_forget openImmersion h_factor F x0

/-- The induced based functor preserves the Artinian local algebra underlying an object. -/
theorem map_obj_base (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    (ξ : Obj openImmersion kToS h_factor X x0) :
    ((map openImmersion h_factor F x0).obj ξ).base = ξ.base :=
  sorry

/-- The induced based functor sends the target object to its fiberwise image. -/
theorem map_obj_target (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    (ξ : Obj openImmersion kToS h_factor X x0) :
    ((map openImmersion h_factor F x0).obj ξ).target =
      (fiberFunctor F (specOver openImmersion ξ.base)).obj ξ.target :=
  sorry

/-- The induced based functor sends the residue arrow to its image under the total functor. -/
theorem map_obj_fromResidue (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    (ξ : Obj openImmersion kToS h_factor X x0) :
    ((map openImmersion h_factor F x0).obj ξ).fromResidue =
      (toFunctor F).map ξ.fromResidue :=
  sorry

/-- The induced based functor preserves the underlying morphism of Artinian local algebras. -/
theorem map_map_baseHom (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    {ξ η : Obj openImmersion kToS h_factor X x0} (f : Hom ξ η) :
    ((map openImmersion h_factor F x0).map f).baseHom = f.baseHom :=
  sorry

/-- The induced based functor sends a reversed arrow to its image under the total functor. -/
theorem map_map_hom (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS))
    {ξ η : Obj openImmersion kToS h_factor X x0} (f : Hom ξ η) :
    ((map openImmersion h_factor F x0).map f).hom = (toFunctor F).map f.hom :=
  sorry

/-- The induced based functor strictly commutes with the Artinian local algebra projections. -/
theorem map_forget (F : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS)) :
    (map openImmersion h_factor F x0).toFunctor ⋙
        forget openImmersion kToS h_factor Y (residueImage F x0) =
      forget openImmersion kToS h_factor X x0 :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
