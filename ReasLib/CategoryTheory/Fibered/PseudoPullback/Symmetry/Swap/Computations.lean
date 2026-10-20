/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Swap.Construction

/-!
# Computations for the explicit pseudo-pullback swap

This leaf exposes the object, morphism, and strict projection formulas of the canonical
`PseudoPullback.swap` functor.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor

universe u v uX vX uY vY uS vS

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

namespace PseudoPullback

noncomputable section

/-- Swapping a pseudo-pullback object retains its common base object. -/
@[simp] theorem swap.obj.base
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    baseObj ((swap F G).obj P) = baseObj P := sorry
/- Proof strategy: unfold the public `swap` owner through its private object constructor and read
the public `baseObj` projection. -/

/-- The first object projection after swapping is the original second object. -/
@[simp] theorem swap.obj.fst
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    fstObj ((swap F G).obj P) = sndObj P := sorry
/- Proof strategy: read the first object projection of the privately assembled swapped
`PseudoPullback.mk`. -/

/-- The second object projection after swapping is the original first object. -/
@[simp] theorem swap.obj.snd
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    sndObj ((swap F G).obj P) = fstObj P := sorry
/- Proof strategy: read the second object projection of the privately assembled swapped
`PseudoPullback.mk`. -/

/-- Swapping reverses the comparison stored by a pseudo-pullback object. -/
@[simp] theorem swap.obj.comparison
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    comparison ((swap F G).obj P) =
      (PseudoPullback.comparisonIsoApp (F := F) (G := G) P).inv := sorry
/- Proof strategy: expose the public comparison projection of the swapped object and identify
the inverse stored in the fibre model through the canonical `comparisonIsoApp` owner. -/

/-- The objectwise comparison isomorphism of a swapped object is the inverse of the original
comparison isomorphism. -/
@[simp]
theorem swap.obj.comparisonIso
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) (P : (PseudoPullback F G).obj) :
    PseudoPullback.comparisonIsoApp (F := G) (G := F) ((swap F G).obj P) =
      (PseudoPullback.comparisonIsoApp (F := F) (G := G) P).symm := sorry

/-- Swapping a pseudo-pullback morphism retains its common base map. -/
@[simp] theorem swap.map.base
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    PseudoPullback.baseMap (F := G) (G := F) ((swap F G).map φ) =
      PseudoPullback.baseMap (F := F) (G := G) φ := sorry
/- Proof strategy: unfold the public `swap` owner and read the common base-map projection of its
private `homMk` assembly. -/

/-- The first morphism projection after swapping is the original second projection. -/
@[simp] theorem swap.map.fst
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    fstMap ((swap F G).map φ) = sndMap φ := sorry
/- Proof strategy: read the first map projection of the privately assembled swapped
`PseudoPullback.Hom.mk`. -/

/-- The second morphism projection after swapping is the original first projection. -/
@[simp] theorem swap.map.snd
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    sndMap ((swap F G).map φ) = fstMap φ := sorry
/- Proof strategy: read the second map projection of the privately assembled swapped
`PseudoPullback.Hom.mk`. -/

/-- Swapping exchanges the first projection with the second. -/
@[simp]
theorem swap.fst (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    swap F G ⋙ PseudoPullback.fst G F = PseudoPullback.snd F G := sorry
/- Proof strategy: ext on underlying functors; the first component of `swapObj` and `swapMap` is
definitionally the original second component. -/

/-- Swapping exchanges the second projection with the first. -/
@[simp]
theorem swap.snd (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    swap F G ⋙ PseudoPullback.snd G F = PseudoPullback.fst F G := sorry
/- Proof strategy: symmetric to `swap.fst`; the swapped second component is the original first. -/

end

end PseudoPullback
end BasedCategory
end CategoryTheory
