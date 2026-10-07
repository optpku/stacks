module

public import ReasLib.CategoryTheory.Fibered.Pullback.Comparison.Composition.Equivalence
public import ReasLib.CategoryTheory.Fibered.Pullback.Map

/-!
# Computations for pullback composition

Underlying based functors, total functors, object and morphism formulas, projection equations,
and naturality with respect to `Pullback.mapCanonical`.
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

/-- The based forward morphism of the fibred reassociation equivalence is the explicit forward
comparison. -/
@[simp]
theorem equivalence.hom.toBasedFunctor :
    FiberedCategoryOver.toBasedFunctor (equivalence u₀ v₀ X).hom =
      forwardBased u₀ v₀ X := sorry

/-- The based inverse morphism of the fibred reassociation equivalence is the explicit inverse
comparison. -/
@[simp]
theorem equivalence.inv.toBasedFunctor :
    FiberedCategoryOver.toBasedFunctor (equivalence u₀ v₀ X).inv =
      inverseBased u₀ v₀ X := sorry

/-- The total forward functor is categorical-pullback reassociation. -/
@[simp]
theorem equivalence.hom.toFunctor :
    FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).hom =
      CategoricalPullback.LeftProjection.forward u₀ v₀ X.p := sorry

/-- The total inverse functor is inverse categorical-pullback reassociation. -/
@[simp]
theorem equivalence.inv.toFunctor :
    FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).inv =
      CategoricalPullback.LeftProjection.inverse u₀ v₀ X.p := sorry

/-- The forward comparison retains the leftmost base object. -/
@[simp]
theorem equivalence.hom.obj.fst
    (x : (FiberedCategoryOver.pullback u₀
      (FiberedCategoryOver.pullback v₀ X)).total) :
    ((FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).hom).obj x).fst =
      x.fst := sorry

/-- The forward comparison retains the final total-category object. -/
@[simp]
theorem equivalence.hom.obj.snd
    (x : (FiberedCategoryOver.pullback u₀
      (FiberedCategoryOver.pullback v₀ X)).total) :
    ((FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).hom).obj x).snd =
      x.snd.snd := sorry

/-- The forward comparison composes the two structural pullback isomorphisms. -/
@[simp]
theorem equivalence.hom.obj.iso
    (x : (FiberedCategoryOver.pullback u₀
      (FiberedCategoryOver.pullback v₀ X)).total) :
    ((FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).hom).obj x).iso =
      v₀.mapIso x.iso ≪≫ x.snd.iso := sorry

/-- On morphisms, the forward comparison retains the leftmost component. -/
@[simp]
theorem equivalence.hom.map.fst
    {x y : (FiberedCategoryOver.pullback u₀
      (FiberedCategoryOver.pullback v₀ X)).total} (f : x ⟶ y) :
    ((FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).hom).map f).fst =
      f.fst := sorry

/-- On morphisms, the forward comparison retains the final component. -/
@[simp]
theorem equivalence.hom.map.snd
    {x y : (FiberedCategoryOver.pullback u₀
      (FiberedCategoryOver.pullback v₀ X)).total} (f : x ⟶ y) :
    ((FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).hom).map f).snd =
      f.snd.snd := sorry

/-- The forward comparison's total functor commutes strictly with projection to `C`. -/
theorem equivalence.hom.compProjection :
    FiberedCategoryOver.toFunctor (equivalence u₀ v₀ X).hom ⋙
        (FiberedCategoryOver.pullback (u₀ ⋙ v₀) X).p =
      (FiberedCategoryOver.pullback u₀
        (FiberedCategoryOver.pullback v₀ X)).p := sorry

/-- The forward pullback-composition comparison is natural in cartesian morphisms of fibred
categories. -/
theorem equivalence.hom.naturality
    {Y : FiberedCategoryOver.{u, v, w, vS} E} (F : X ⟶ Y) :
    (equivalence u₀ v₀ X).hom ≫ Pullback.mapCanonical (u₀ ⋙ v₀) F =
      Pullback.mapCanonical u₀ (Pullback.mapCanonical v₀ F) ≫
        (equivalence u₀ v₀ Y).hom := sorry

/-- The inverse pullback-composition comparison is natural in cartesian morphisms of fibred
categories. -/
theorem equivalence.inv.naturality
    {Y : FiberedCategoryOver.{u, v, w, vS} E} (F : X ⟶ Y) :
    (equivalence u₀ v₀ X).inv ≫
        Pullback.mapCanonical u₀ (Pullback.mapCanonical v₀ F) =
      Pullback.mapCanonical (u₀ ⋙ v₀) F ≫
        (equivalence u₀ v₀ Y).inv := sorry

end CategoryTheory.FiberedCategoryOver.Pullback.Comp
