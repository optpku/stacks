module

public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.RelativeDiagonal.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative inertia comparison inverse construction

This module constructs the explicit inverse from the self-pseudo-pullback of the
relative diagonal to relative inertia. Computation lemmas for its structural
components live in `DiagonalComparison.Inverse.Computations`.
-/

open CategoryTheory
open CategoryTheory.Limits
open BasedCategory
open BasedFunctor
open scoped Bicategory

universe uC vC uS vS uS' vS'

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

namespace BasedFunctor

open Functor.Fiber

variable {X Y : BasedCategory C}

/-- The structural isomorphism carried by an object of the self-pullback of the relative
diagonal, regarded as an isomorphism in the inner pseudo-pullback category. -/
@[stacks 034H "diagonal-comparison inverse inner isomorphism"]
noncomputable def RelativeInertia.diagonalComparison.inverse.innerIso (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (relativeDiagonal F).obj
        (PseudoPullback.fstObj P) ≅
      (relativeDiagonal F).obj
        (PseudoPullback.sndObj P) :=
  (fiberInclusion :
      Functor.Fiber
          (PseudoPullback F F).p
          (PseudoPullback.baseObj P) ⥤
        (PseudoPullback F F).obj).mapIso
    (PseudoPullback.fiberObj P).iso

/-- The first-component isomorphism extracted from the structural isomorphism of an object in
the self-pullback of the relative diagonal. -/
@[stacks 034H "diagonal-comparison inverse first component isomorphism"]
noncomputable def RelativeInertia.diagonalComparison.inverse.fstIso (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.fstObj P ≅ PseudoPullback.sndObj P :=
  (PseudoPullback.fst F F).toFunctor.mapIso
    (RelativeInertia.diagonalComparison.inverse.innerIso F P)

/-- The second-component isomorphism extracted from the structural isomorphism of an object in
the self-pullback of the relative diagonal. -/
@[stacks 034H "diagonal-comparison inverse second component isomorphism"]
noncomputable def RelativeInertia.diagonalComparison.inverse.sndIso (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.fstObj P ≅ PseudoPullback.sndObj P :=
  (PseudoPullback.snd F F).toFunctor.mapIso
    (RelativeInertia.diagonalComparison.inverse.innerIso F P)

/-- The relative-inertia automorphism recovered from a self-pullback object is the quotient of
its first structural component by its second structural component. -/
@[stacks 034H "diagonal-comparison inverse recovered automorphism"]
noncomputable def RelativeInertia.diagonalComparison.inverse.aut (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    Aut (PseudoPullback.fstObj P) :=
  RelativeInertia.diagonalComparison.inverse.fstIso F P ≪≫
    (RelativeInertia.diagonalComparison.inverse.sndIso F P).symm

/-- The automorphism recovered from a self-pullback object becomes the identity after applying
the original based functor. -/
@[stacks 034H "diagonal-comparison inverse automorphism kernel condition"]
theorem RelativeInertia.diagonalComparison.inverse.aut.map_eq_one (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    F.toFunctor.mapAut
        (PseudoPullback.fstObj P)
        (RelativeInertia.diagonalComparison.inverse.aut F P) =
      1 := sorry

/-- Recover a relative-inertia object from an object of the self-pullback of the relative
diagonal. -/
@[stacks 034H "diagonal-comparison inverse object"]
noncomputable def RelativeInertia.diagonalComparison.inverse.obj (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    CategoryTheory.RelativeInertia F.toFunctor :=
  CategoryTheory.RelativeInertia.mk
    (Inertia.mk (PseudoPullback.fstObj P) (RelativeInertia.diagonalComparison.inverse.aut F P))
    (RelativeInertia.diagonalComparison.inverse.aut.map_eq_one F P)

/-- The first component of a self-pullback morphism intertwines the recovered relative-inertia
automorphisms. -/
@[stacks 034H "diagonal-comparison inverse map naturality"]
theorem RelativeInertia.diagonalComparison.inverse.map.naturality (F : X ⥤ᵇ Y)
    {P Q : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj}
    (φ : P ⟶ Q) :
    (RelativeInertia.diagonalComparison.inverse.aut F P).hom ≫
        PseudoPullback.fstMap φ =
      PseudoPullback.fstMap φ ≫
        (RelativeInertia.diagonalComparison.inverse.aut F Q).hom := sorry

/-- The inverse automorphisms satisfy the corresponding reverse intertwining equation. -/
@[reassoc, stacks 034H "diagonal-comparison inverse map inverse naturality"]
theorem RelativeInertia.diagonalComparison.inverse.map.invNaturality (F : X ⥤ᵇ Y)
    {P Q : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj}
    (φ : P ⟶ Q) :
    (RelativeInertia.diagonalComparison.inverse.aut F P).inv ≫
        PseudoPullback.fstMap φ =
      PseudoPullback.fstMap φ ≫
        (RelativeInertia.diagonalComparison.inverse.aut F Q).inv := sorry

/-- Recover a relative-inertia morphism by taking the first component of a morphism in the
self-pullback of the relative diagonal. -/
@[stacks 034H "diagonal-comparison inverse map"]
noncomputable def RelativeInertia.diagonalComparison.inverse.map (F : X ⥤ᵇ Y)
    {P Q : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj}
    (φ : P ⟶ Q) :
    RelativeInertia.diagonalComparison.inverse.obj F P ⟶
      RelativeInertia.diagonalComparison.inverse.obj F Q :=
  CategoryTheory.RelativeInertia.homMk
    F.toFunctor
    (PseudoPullback.fstMap φ)
    (RelativeInertia.diagonalComparison.inverse.map.naturality F φ)

/-- The recovered relative-inertia map preserves identity morphisms. -/
@[stacks 034H "diagonal-comparison inverse map identity"]
theorem RelativeInertia.diagonalComparison.inverse.map.id (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    RelativeInertia.diagonalComparison.inverse.map F (𝟙 P) =
      𝟙 (RelativeInertia.diagonalComparison.inverse.obj F P) := sorry

/-- The recovered relative-inertia map preserves composition. -/
@[stacks 034H "diagonal-comparison inverse map composition"]
theorem RelativeInertia.diagonalComparison.inverse.map.comp (F : X ⥤ᵇ Y)
    {P Q R : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    RelativeInertia.diagonalComparison.inverse.map F (φ ≫ ψ) =
      RelativeInertia.diagonalComparison.inverse.map F φ ≫
        RelativeInertia.diagonalComparison.inverse.map F ψ := sorry

/-- The explicit functor recovering relative inertia from the self-pullback of the relative
diagonal. -/
@[stacks 034H "diagonal-comparison inverse underlying functor"]
noncomputable def RelativeInertia.diagonalComparison.inverse.toFunctor (F : X ⥤ᵇ Y) :
    (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj ⥤
      CategoryTheory.RelativeInertia F.toFunctor where
  obj := RelativeInertia.diagonalComparison.inverse.obj F
  map := RelativeInertia.diagonalComparison.inverse.map F
  map_id := RelativeInertia.diagonalComparison.inverse.map.id F
  map_comp := RelativeInertia.diagonalComparison.inverse.map.comp F

/-- The explicit comparison inverse commutes with the projections to the common base. -/
@[stacks 034H "diagonal-comparison inverse projection compatibility"]
theorem RelativeInertia.diagonalComparison.inverse.toFunctor.comm (F : X ⥤ᵇ Y) :
    RelativeInertia.diagonalComparison.inverse.toFunctor F ⋙
        CategoryTheory.RelativeInertia.projection F.toFunctor X.p =
      (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).p := sorry

/-- The explicit based inverse to the relative-inertia comparison. -/
@[stacks 034H "inverse relative-inertia diagonal comparison"]
noncomputable def RelativeInertia.diagonalComparison.inverse (F : X ⥤ᵇ Y) :
    PseudoPullback (relativeDiagonal F) (relativeDiagonal F) ⥤ᵇ
      BasedCategory.ofFunctor
        (CategoryTheory.RelativeInertia.projection F.toFunctor X.p) where
  toFunctor := RelativeInertia.diagonalComparison.inverse.toFunctor F
  w := RelativeInertia.diagonalComparison.inverse.toFunctor.comm F

end BasedFunctor

end CategoryTheory
