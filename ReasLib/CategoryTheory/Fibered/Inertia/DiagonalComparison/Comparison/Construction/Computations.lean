/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Comparison.Construction.Naturality
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative inertia diagonal-comparison computations

This leaf exposes the object, morphism, and inner-automorphism projections of
`BasedFunctor.RelativeInertia.diagonalComparison`.  The construction and naturality owners are
available through the preceding focused imports without requiring this readout layer.
-/

open CategoryTheory
open CategoryTheory.Limits
open BasedCategory
open BasedFunctor
open scoped Bicategory

universe uC vC

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

namespace BasedFunctor

open Functor.Fiber

variable {X Y : BasedCategory C}

/-- The object map of the bundled comparison is the neutral diagonal-comparison object owner. -/
@[stacks 034H "relative-inertia diagonal-comparison object owner"]
theorem RelativeInertia.diagonalComparison.obj_eq (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    (RelativeInertia.diagonalComparison F).obj A =
      RelativeInertia.diagonalComparisonObj F A := sorry

/-- The inertia comparison retains the base object of the underlying inertia object. -/
@[simp, stacks 034H "relative-inertia diagonal-comparison base object"]
theorem RelativeInertia.diagonalComparison.obj.base (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    PseudoPullback.baseObj ((RelativeInertia.diagonalComparison F).obj A) =
      X.p.obj A.obj := sorry
/- Proof strategy: unfold `RelativeInertia.diagonalComparison` through its private constructor and
read the public outer `PseudoPullback.baseObj` projection. -/

/-- The first object projection of the inertia comparison is the underlying inertia object. -/
@[simp, stacks 034H "relative-inertia diagonal-comparison first object"]
theorem RelativeInertia.diagonalComparison.obj.fst (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    PseudoPullback.fstObj ((RelativeInertia.diagonalComparison F).obj A) = A.obj := sorry
/- Proof strategy: read the first object projection of the outer public pseudo-pullback object. -/

/-- The second object projection of the inertia comparison is the underlying inertia object. -/
@[simp, stacks 034H "relative-inertia diagonal-comparison second object"]
theorem RelativeInertia.diagonalComparison.obj.snd (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    PseudoPullback.sndObj ((RelativeInertia.diagonalComparison F).obj A) = A.obj := sorry
/- Proof strategy: read the second object projection of the outer public pseudo-pullback object. -/

/-- The common base map of the inertia comparison is the image of its underlying arrow. -/
@[simp, stacks 034H "relative-inertia diagonal-comparison base map"]
theorem RelativeInertia.diagonalComparison.map.base (F : X ⥤ᵇ Y)
    {A B : CategoryTheory.RelativeInertia F.toFunctor} (f : A ⟶ B) :
    PseudoPullback.baseMap ((RelativeInertia.diagonalComparison F).map f) =
        X.p.map (CategoryTheory.RelativeInertia.hom f) := sorry
/- Proof strategy: read the common base-map projection of the outer
`PseudoPullback.Hom.mk`. -/

/-- The first morphism projection of the inertia comparison is its underlying arrow. -/
@[simp, stacks 034H "relative-inertia diagonal-comparison first map"]
theorem RelativeInertia.diagonalComparison.map.fst (F : X ⥤ᵇ Y)
    {A B : CategoryTheory.RelativeInertia F.toFunctor} (f : A ⟶ B) :
    PseudoPullback.fstMap ((RelativeInertia.diagonalComparison F).map f) =
      CategoryTheory.RelativeInertia.hom f := sorry
/- Proof strategy: read the first map projection of the outer `PseudoPullback.Hom.mk`. -/

/-- The second morphism projection of the inertia comparison is its underlying arrow. -/
@[simp, stacks 034H "relative-inertia diagonal-comparison second map"]
theorem RelativeInertia.diagonalComparison.map.snd (F : X ⥤ᵇ Y)
    {A B : CategoryTheory.RelativeInertia F.toFunctor} (f : A ⟶ B) :
    PseudoPullback.sndMap ((RelativeInertia.diagonalComparison F).map f) =
      CategoryTheory.RelativeInertia.hom f := sorry
/- Proof strategy: read the second map projection of the outer `PseudoPullback.Hom.mk`. -/

/-- The comparison automorphism has identity common base component in the inner
pseudo-pullback. -/
@[simp, stacks 034H "relative-inertia diagonal-comparison automorphism base map"]
theorem RelativeInertia.diagonalComparison.obj.aut.base (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    PseudoPullback.baseMap
      (PseudoPullback.comparison ((RelativeInertia.diagonalComparison F).obj A)) =
        𝟙 (X.p.obj A.obj) := sorry
/- Proof strategy: expose the inner pseudo-pullback morphism stored by the outer comparison and
read its common base-map projection. -/

/-- The first inner projection of the comparison automorphism is the chosen inertia
automorphism. -/
@[simp, stacks 034H "relative-inertia diagonal-comparison automorphism first map"]
theorem RelativeInertia.diagonalComparison.obj.aut.fst (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    PseudoPullback.fstMap
      (PseudoPullback.comparison ((RelativeInertia.diagonalComparison F).obj A)) = A.aut.hom := sorry
/- Proof strategy: expose the inner pseudo-pullback morphism and read the first projection of its
public `PseudoPullback.Hom.mk` representation. -/

/-- The second inner projection of the comparison automorphism is the identity. -/
@[simp, stacks 034H "relative-inertia diagonal-comparison automorphism second map"]
theorem RelativeInertia.diagonalComparison.obj.aut.snd (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    PseudoPullback.sndMap
      (PseudoPullback.comparison ((RelativeInertia.diagonalComparison F).obj A)) = 𝟙 A.obj := sorry
/- Proof strategy: expose the inner pseudo-pullback morphism and read the second projection of its
public `PseudoPullback.Hom.mk` representation. -/

/-- The inverse comparison automorphism has identity common base component in the inner
pseudo-pullback. -/
@[simp, stacks 034H "relative-inertia diagonal-comparison inverse automorphism base map"]
theorem RelativeInertia.diagonalComparison.obj.aut.inv.base (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    PseudoPullback.baseMap
      (PseudoPullback.comparisonIsoApp ((RelativeInertia.diagonalComparison F).obj A)).inv =
        𝟙 (X.p.obj A.obj) := sorry

/-- The first inner projection of the inverse comparison automorphism is the inverse inertia
automorphism. -/
@[simp, stacks 034H "relative-inertia diagonal-comparison inverse automorphism first map"]
theorem RelativeInertia.diagonalComparison.obj.aut.inv.fst (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    PseudoPullback.fstMap
      (PseudoPullback.comparisonIsoApp ((RelativeInertia.diagonalComparison F).obj A)).inv = A.aut.inv := sorry

/-- The second inner projection of the inverse comparison automorphism is the identity. -/
@[simp, stacks 034H "relative-inertia diagonal-comparison inverse automorphism second map"]
theorem RelativeInertia.diagonalComparison.obj.aut.inv.snd (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    PseudoPullback.sndMap
      (PseudoPullback.comparisonIsoApp ((RelativeInertia.diagonalComparison F).obj A)).inv = 𝟙 A.obj := sorry

end BasedFunctor

end CategoryTheory
