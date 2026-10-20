module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Cosimplicial
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Equiv
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

/-!
# Change of rings for modules over cosimplicial algebras

This file constructs degreewise scalar extension for modules over cosimplicial
commutative algebras and its restriction to cartesian modules.
-/

@[expose] public section

open CategoryTheory
open scoped ChangeOfRings TensorProduct

noncomputable section

universe u

namespace CosimplicialAlgebra

variable {R : Type u} [CommRing R]
variable {A B : CosimplicialObject (CommAlgCat.{u} R)}

/-- The morphism of underlying commutative-ring presheaves induced by a morphism of
cosimplicial commutative algebras. -/
def underlyingMap (f : A ⟶ B) : commRingPresheaf A ⟶ commRingPresheaf B :=
  Functor.whiskerLeft (unopUnop SimplexCategory)
    (Functor.whiskerRight f (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}))

/-- Naturality of the underlying ring map, written as an equality of ring homomorphisms. -/
theorem underlyingMap_naturality (f : A ⟶ B) {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ}
    (g : X ⟶ Y) :
    ((underlyingMap f).app Y).hom.comp ((commRingPresheaf A).map g).hom =
      ((commRingPresheaf B).map g).hom.comp ((underlyingMap f).app X).hom := sorry

namespace Module

/-- The structure map on the degreewise scalar extension of a module over a cosimplicial
algebra. -/
noncomputable def extensionStructureMap (f : A ⟶ B) (M : Module A)
    {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) :
    (ModuleCat.extendScalars ((underlyingMap f).app X).hom).obj (M.obj X) ⟶
      (ModuleCat.restrictScalars ((commRingPresheaf B).map g).hom).obj
        ((ModuleCat.extendScalars ((underlyingMap f).app Y).hom).obj (M.obj Y)) :=
  let extendedTarget :=
    (ModuleCat.extendScalars ((underlyingMap f).app Y).hom).obj (M.obj Y)
  let target :=
    (ModuleCat.restrictScalars ((commRingPresheaf B).map g).hom).obj extendedTarget
  let generator : M.obj X ⟶
      (ModuleCat.restrictScalars ((underlyingMap f).app X).hom).obj target :=
    M.map g ≫
      (ModuleCat.restrictScalars ((commRingPresheaf A).map g).hom).map
        ((ModuleCat.extendRestrictScalarsAdj
          ((underlyingMap f).app Y).hom).unit.app (M.obj Y)) ≫
      (ModuleCat.restrictScalarsComp'App
        ((commRingPresheaf A).map g).hom ((underlyingMap f).app Y).hom
        (((underlyingMap f).app Y).hom.comp ((commRingPresheaf A).map g).hom)
        rfl extendedTarget).inv ≫
      (eqToIso (congrArg
        (fun h : (commRingPresheaf A).obj X →+* (commRingPresheaf B).obj Y ↦
          (ModuleCat.restrictScalars h).obj extendedTarget)
        (underlyingMap_naturality f g))).hom ≫
      (ModuleCat.restrictScalarsComp'App
        ((underlyingMap f).app X).hom ((commRingPresheaf B).map g).hom
        (((commRingPresheaf B).map g).hom.comp ((underlyingMap f).app X).hom)
        rfl extendedTarget).hom
  ((ModuleCat.extendRestrictScalarsAdj ((underlyingMap f).app X).hom).homEquiv _ _).symm
    generator

/-- Degreewise scalar extension of one module over a cosimplicial algebra. -/
noncomputable def extensionObj (f : A ⟶ B) (M : Module A) : Module B where
  obj X := (ModuleCat.extendScalars ((underlyingMap f).app X).hom).obj (M.obj X)
  map g := extensionStructureMap f M g
  map_id := sorry
  map_comp := sorry

/-- Evaluation of `extensionObj` is ordinary scalar extension in the chosen degree. -/
theorem extensionObj_obj (f : A ⟶ B) (M : Module A) (X : (SimplexCategoryᵒᵖ)ᵒᵖ) :
    (extensionObj f M).obj X =
      (ModuleCat.extendScalars ((underlyingMap f).app X).hom).obj (M.obj X) := sorry

/-- Degreewise scalar extension of a morphism of modules over a cosimplicial algebra. -/
noncomputable def extensionHom (f : A ⟶ B) {M N : Module A} (α : M ⟶ N) :
    extensionObj f M ⟶ extensionObj f N where
  app X := (ModuleCat.extendScalars ((underlyingMap f).app X).hom).map (α.app X)
  naturality := sorry

/-- The component of `extensionHom` is ordinary scalar extension. -/
theorem extensionHom_app (f : A ⟶ B) {M N : Module A} (α : M ⟶ N)
    (X : (SimplexCategoryᵒᵖ)ᵒᵖ) :
    PresheafOfModules.Hom.app (extensionHom f α) X =
      (ModuleCat.extendScalars ((underlyingMap f).app X).hom).map (α.app X) := sorry

/-- Degreewise extension of scalars along a morphism of cosimplicial commutative algebras. -/
noncomputable def extension (f : A ⟶ B) : Module A ⥤ Module B where
  obj := extensionObj f
  map := extensionHom f
  map_id := sorry
  map_comp := sorry

/-- Extension along a cosimplicial homotopy equivalence preserves cartesianness. -/
theorem extension_isCartesian
    (e : CosimplicialObject.HomotopyEquiv A B) (M : Module A)
    (hM : IsCartesian M) : IsCartesian ((extension e.hom).obj M) := sorry

end Module

namespace CartesianModule

/-- Extension of scalars along a homotopy equivalence of small cosimplicial algebras,
restricted to cartesian modules. -/
noncomputable def extension (e : CosimplicialObject.HomotopyEquiv A B) :
    CartesianModule A ⥤ CartesianModule B :=
  ObjectProperty.FullSubcategory.restrict (Module.extension e.hom)
    (fun M hM ↦ Module.extension_isCartesian e M hM)

/-- Forgetting the cartesian property from `extension` gives ordinary extension of scalars. -/
theorem extension_obj (e : CosimplicialObject.HomotopyEquiv A B)
    (M : CartesianModule A) :
    ((extension e).obj M).obj = (Module.extension e.hom).obj M.obj := sorry

/-- Extension of scalars along a cosimplicial homotopy equivalence is an equivalence on
cartesian modules. -/
instance extension_isEquivalence (e : CosimplicialObject.HomotopyEquiv A B) :
    (extension e).IsEquivalence := sorry

end CartesianModule

end CosimplicialAlgebra
