/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
      ((commRingPresheaf B).map g).hom.comp ((underlyingMap f).app X).hom :=
  congrArg CommRingCat.Hom.hom ((underlyingMap f).naturality g)

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

/-- The comparison after scalar extension, via composition of scalar extensions and
the original module's base-change map. -/
noncomputable def extensionBaseChangeHom (f : A ⟶ B) (M : Module A)
    {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) :
    (ModuleCat.extendScalars ((commRingPresheaf B).map g).hom).obj
        ((ModuleCat.extendScalars ((underlyingMap f).app X).hom).obj (M.obj X)) ⟶
      (ModuleCat.extendScalars ((underlyingMap f).app Y).hom).obj (M.obj Y) :=
  (ModuleCat.extendScalarsComp ((underlyingMap f).app X).hom
    ((commRingPresheaf B).map g).hom).inv.app (M.obj X) ≫
  eqToHom (congrArg
    (fun h : (commRingPresheaf A).obj X →+* (commRingPresheaf B).obj Y ↦
      (ModuleCat.extendScalars h).obj (M.obj X))
    (underlyingMap_naturality f g).symm) ≫
  (ModuleCat.extendScalarsComp ((commRingPresheaf A).map g).hom
    ((underlyingMap f).app Y).hom).hom.app (M.obj X) ≫
  (ModuleCat.extendScalars ((underlyingMap f).app Y).hom).map
    (PresheafOfModules.BaseChange.map (commRingPresheaf A) M g)

/-- Reverse the scalar-extension comparison, using only the inverse supplied by `hM` and
the native scalar-extension composition isomorphisms. -/
noncomputable def extensionBaseChangeInv (f : A ⟶ B) (M : Module A)
    (hM : IsCartesian M) {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) :
    (ModuleCat.extendScalars ((underlyingMap f).app Y).hom).obj (M.obj Y) ⟶
      (ModuleCat.extendScalars ((commRingPresheaf B).map g).hom).obj
        ((ModuleCat.extendScalars ((underlyingMap f).app X).hom).obj (M.obj X)) :=
  (ModuleCat.extendScalars ((underlyingMap f).app Y).hom).map
    (@CategoryTheory.inv _ _ _ _
      (PresheafOfModules.BaseChange.map (commRingPresheaf A) M g) (hM g)) ≫
  (ModuleCat.extendScalarsComp ((commRingPresheaf A).map g).hom
    ((underlyingMap f).app Y).hom).inv.app (M.obj X) ≫
  eqToHom (congrArg
    (fun h : (commRingPresheaf A).obj X →+* (commRingPresheaf B).obj Y ↦
      (ModuleCat.extendScalars h).obj (M.obj X))
    (underlyingMap_naturality f g)) ≫
  (ModuleCat.extendScalarsComp ((underlyingMap f).app X).hom
    ((commRingPresheaf B).map g).hom).hom.app (M.obj X)

/-- The cartesian comparison after scalar extension. No homotopy equivalence is needed to
preserve cartesianness; both maps are constructed independently of the inverse-law proofs. -/
noncomputable def extensionBaseChangeIso (f : A ⟶ B) (M : Module A)
    (hM : IsCartesian M) {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) :
    (PresheafOfModules.BaseChange.functor (commRingPresheaf B) g).obj
        ((extension f).obj M) ≅ ((extension f).obj M).obj Y where
  hom := extensionBaseChangeHom f M g
  inv := extensionBaseChangeInv f M hM g
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The displayed comparison is the canonical base-change map of the extended module. -/
theorem extensionBaseChangeIso_hom (f : A ⟶ B) (M : Module A)
    (hM : IsCartesian M) {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (g : X ⟶ Y) :
    (extensionBaseChangeIso f M hM g).hom =
      PresheafOfModules.BaseChange.map (commRingPresheaf B) ((extension f).obj M) g := sorry

/-- Scalar extension along any cosimplicial algebra map preserves cartesianness, storing the
inverse of the displayed scalar-extension comparison. -/
theorem extension_isCartesian_of_isCartesian (f : A ⟶ B) (M : Module A)
    (hM : IsCartesian M) : IsCartesian ((extension f).obj M) := by
  intro X Y g
  refine ⟨⟨(extensionBaseChangeIso f M hM g).inv, ?_, ?_⟩⟩
  · rw [← extensionBaseChangeIso_hom f M hM g]
    exact (extensionBaseChangeIso f M hM g).hom_inv_id
  · rw [← extensionBaseChangeIso_hom f M hM g]
    exact (extensionBaseChangeIso f M hM g).inv_hom_id

/-- Extension along a cosimplicial homotopy equivalence preserves cartesianness. -/
theorem extension_isCartesian
    (e : CosimplicialObject.HomotopyEquiv A B) (M : Module A)
    (hM : IsCartesian M) : IsCartesian ((extension e.hom).obj M) :=
  extension_isCartesian_of_isCartesian e.hom M hM

end Module

namespace CartesianModule

/-- Extension of scalars along a homotopy equivalence of small cosimplicial algebras,
restricted to cartesian modules. -/
noncomputable def extension (e : CosimplicialObject.HomotopyEquiv A B) :
    CartesianModule A ⥤ CartesianModule B :=
  ObjectProperty.FullSubcategory.restrict (Module.extension e.hom)
    (fun M hM ↦ Module.extension_isCartesian e M hM)

/-- The public comparison of an output of `extension` uses the explicitly constructed inverse. -/
theorem extension_baseChangeIso_inv (e : CosimplicialObject.HomotopyEquiv A B)
    (M : CartesianModule A) {n m : SimplexCategory} (g : n ⟶ m) :
    (baseChangeIso ((extension e).obj M) g).inv =
      (Module.extensionBaseChangeIso e.hom M.obj M.property g.op.op).inv := by
  apply (Iso.inv_eq_inv (baseChangeIso ((extension e).obj M) g)
    (Module.extensionBaseChangeIso e.hom M.obj M.property g.op.op)).2
  exact (Module.extensionBaseChangeIso_hom e.hom M.obj M.property g.op.op).symm

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
