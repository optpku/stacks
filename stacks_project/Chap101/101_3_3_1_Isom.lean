module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex.NatIso
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.CategoryTheory.Fibered.HomPresheaf.Isom
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Isom
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.StrongTrans
public import stacks_project.Chap94.Definition_94_12_1_Representable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism-presheaf maps along morphisms of groupoid fibrations

A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids induces
`Isom_X(x, x') ⟶ Isom_Y(f(x), f(x'))`. A fibrewise isomorphism
`α : f(x) ≅ f(x')` transposes to a section of the target over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- Size-stable isomorphism presheaf `Isom_X(x, x')` on `Over T`. -/
abbrev isom {T : Over S} (x x' : X.p.Fiber T) :
    (Over T)ᵒᵖ ⥤ Type (u + 1) :=
  Functor.isomorphismPresheafULift X.p x x'

/-- Strong transformation of fibre pseudofunctors induced by a morphism of
categories fibred in groupoids. -/
def homStrongTrans (f : X ⟶ Y) :
    Pseudofunctor.StrongTrans
      (Functor.fiberPseudofunctor X.p) (Functor.fiberPseudofunctor Y.p) where
  app U := (fiberFunctor f (unop U.as)).toCatHom
  naturality g :=
    Cat.Hom.isoMk
      (CartesianBasedFunctor.Reindex.natIso (toCartesianBasedFunctor f)
        (Functor.Cleavage.ofIsFibered X.p) (Functor.Cleavage.ofIsFibered Y.p)
        g.as.unop).symm
  naturality_naturality := sorry
  naturality_id := sorry
  naturality_comp := sorry

/-- Unlifted isomorphism-presheaf map induced by `f` at a pair of fibre objects. -/
def isomMapHom (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T) :
    Functor.isomorphismPresheaf X.p x x' ⟶
      Functor.isomorphismPresheaf Y.p
        ((fiberFunctor f T).obj x) ((fiberFunctor f T).obj x') where
  app W :=
    TypeCat.ofHom fun φ =>
      ⟨(Pseudofunctor.StrongTrans.presheafHomMap (homStrongTrans f) x x').app W φ.1,
        sorry⟩
  naturality := sorry

/-- The map `Isom_X(x, x') ⟶ Isom_Y(f(x), f(x'))` induced by `f`. -/
def isomMap (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T) :
    isom x x' ⟶ isom ((fiberFunctor f T).obj x) ((fiberFunctor f T).obj x') :=
  whiskerRight (isomMapHom f x x') uliftFunctor.{u + 1, u}

/-- Evaluation of `isomMap` on the underlying Hom-presheaf section is the
strong-transformation action. -/
theorem isomMap_apply (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (W : (Over T)ᵒᵖ) (φ : (isom x x').obj W) :
    ((isomMap f x x').app W φ).down.1 =
      (Pseudofunctor.StrongTrans.presheafHomMap (homStrongTrans f) x x').app W
        φ.down.1 :=
  sorry

/-- Yoneda transpose of a fibrewise isomorphism `α : f(x) ≅ f(x')`, as a map from the
identity slice of `T`. -/
def alphaSection (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    yoneda.obj (Over.mk (𝟙 T)) ⋙ uliftFunctor.{u + 1, u} ⟶
      isom ((fiberFunctor f T).obj x) ((fiberFunctor f T).obj x') :=
  whiskerRight
    (yonedaEquiv.symm
      (⟨(Functor.fiberPseudofunctor Y.p).presheafHomObjHomEquiv α.hom, sorry⟩ :
        (Functor.isomorphismPresheaf Y.p ((fiberFunctor f T).obj x)
            ((fiberFunctor f T).obj x')).obj
          (op (Over.mk (𝟙 T)))))
    uliftFunctor.{u + 1, u}

/-- The identity-slice component of `alphaSection` is the packaged isomorphism `α`. -/
theorem alphaSection_app (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    ((alphaSection f x x' α).app (op (Over.mk (𝟙 T)))
        (ULift.up (𝟙 (Over.mk (𝟙 T))))).down.1 =
      (Functor.fiberPseudofunctor Y.p).presheafHomObjHomEquiv α.hom :=
  sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal
