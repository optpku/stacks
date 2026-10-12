/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pullback.Comparison.Composition.Equivalence
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber.Action

/-!
# Inverse computations for pullback composition

Object, morphism, and projection formulas for the inverse of the fibred pullback-composition
equivalence.
-/

@[expose] public section

noncomputable section

open CategoryTheory.Limits
open scoped CategoryTheory.Bicategory

namespace CategoryTheory.FiberedCategoryOver.Pullback.Comp

universe u v w vS

variable {C D E : Type u}
variable [Category.{v} C] [Category.{v} D] [Category.{v} E]
variable (u₀ : C ⥤ D) (v₀ : D ⥤ E)
variable (X : FiberedCategoryOver.{u, v, w, vS} E)

/-- The inverse comparison retains the leftmost base object. -/
@[simp]
theorem equivalence.inv.obj.fst
    (x : (FiberedCategoryOver.pullback (u₀ ⋙ v₀) X).total) :
    ((FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).inv).obj x).fst =
      x.fst := sorry

/-- The inverse comparison inserts `u₀.obj x.fst` as the middle object. -/
@[simp]
theorem equivalence.inv.obj.sndFst
    (x : (FiberedCategoryOver.pullback (u₀ ⋙ v₀) X).total) :
    ((FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).inv).obj x).snd.fst =
      u₀.obj x.fst := sorry

/-- The inverse comparison retains the final total-category object. -/
@[simp]
theorem equivalence.inv.obj.sndSnd
    (x : (FiberedCategoryOver.pullback (u₀ ⋙ v₀) X).total) :
    ((FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).inv).obj x).snd.snd =
      x.snd := sorry

/-- The inner structural isomorphism inserted by the inverse comparison is the original
composite-pullback structural isomorphism. -/
@[simp]
theorem equivalence.inv.obj.sndIso
    (x : (FiberedCategoryOver.pullback (u₀ ⋙ v₀) X).total) :
    ((FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).inv).obj x).snd.iso =
      x.iso := sorry

/-- The outer structural isomorphism inserted by the inverse comparison is the identity. -/
@[simp]
theorem equivalence.inv.obj.iso
    (x : (FiberedCategoryOver.pullback (u₀ ⋙ v₀) X).total) :
    ((FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).inv).obj x).iso =
      Iso.refl (u₀.obj x.fst) := sorry

/-- On morphisms, the inverse comparison retains the leftmost component. -/
@[simp]
theorem equivalence.inv.map.fst
    {x y : (FiberedCategoryOver.pullback (u₀ ⋙ v₀) X).total} (f : x ⟶ y) :
    ((FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).inv).map f).fst =
      f.fst := sorry

/-- On the inserted middle component, the inverse comparison applies `u₀`. -/
@[simp]
theorem equivalence.inv.map.sndFst
    {x y : (FiberedCategoryOver.pullback (u₀ ⋙ v₀) X).total} (f : x ⟶ y) :
    ((FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).inv).map f).snd.fst =
      u₀.map f.fst := sorry

/-- On the final component, the inverse comparison retains the supplied morphism. -/
@[simp]
theorem equivalence.inv.map.sndSnd
    {x y : (FiberedCategoryOver.pullback (u₀ ⋙ v₀) X).total} (f : x ⟶ y) :
    ((FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).inv).map f).snd.snd =
      f.snd := sorry

/-- The inverse comparison's total functor commutes strictly with projection to `C`. -/
theorem equivalence.inv.compProjection :
    FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).inv ⋙
        (FiberedCategoryOver.pullback u₀
          (FiberedCategoryOver.pullback v₀ X)).p =
      (FiberedCategoryOver.pullback (u₀ ⋙ v₀) X).p := sorry

end CategoryTheory.FiberedCategoryOver.Pullback.Comp
