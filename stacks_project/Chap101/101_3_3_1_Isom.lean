/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Diagonal.Isom

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

#check (isom : ∀ {T : Over S} (x x' : X.p.Fiber T),
    (Over T)ᵒᵖ ⥤ Type (u + 1))

#check (homStrongTrans : ∀ (f : X ⟶ Y),
    Pseudofunctor.StrongTrans
      (Functor.fiberPseudofunctor X.p) (Functor.fiberPseudofunctor Y.p))

#check (isomMapHom : ∀ (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T),
    Functor.isomorphismPresheaf X.p x x' ⟶
      Functor.isomorphismPresheaf Y.p
        ((fiberFunctor f T).obj x) ((fiberFunctor f T).obj x'))

#check (isomMap : ∀ (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T),
    isom x x' ⟶ isom ((fiberFunctor f T).obj x) ((fiberFunctor f T).obj x'))

#check (isomMap_apply : ∀ (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (W : (Over T)ᵒᵖ) (φ : (isom x x').obj W),
    ((isomMap f x x').app W φ).down.1 =
      (Pseudofunctor.StrongTrans.presheafHomMap (homStrongTrans f) x x').app W
        φ.down.1)

#check (alphaSection : ∀ (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x'),
    yoneda.obj (Over.mk (𝟙 T)) ⋙ uliftFunctor.{u + 1, u} ⟶
      isom ((fiberFunctor f T).obj x) ((fiberFunctor f T).obj x'))

#check (alphaSection_app : ∀ (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x'),
    ((alphaSection f x x' α).app (op (Over.mk (𝟙 T)))
        (ULift.up (𝟙 (Over.mk (𝟙 T))))).down.1 =
      (Functor.fiberPseudofunctor Y.p).presheafHomObjHomEquiv α.hom)

end CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal
