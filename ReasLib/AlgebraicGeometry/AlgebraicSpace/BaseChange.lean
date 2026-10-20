module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Resize
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CostructuredArrow

/-!
# Base change of categories over schemes to an algebraic-space base

For a category equipped with a functor to schemes, this file constructs the category of
objects whose base scheme maps to the algebraic space over `Spec ℤ`.
The owner `categoryBaseChange` keeps this relative category distinct from
`AlgebraicSpace.baseChange`, which pulls an algebraic space back along a scheme morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoricalPullback
open scoped CategoryTheory.Limits.CategoricalPullback

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

namespace categoryBaseChange

/-- The functor sending a scheme over `Spec ℤ` to its representable algebraic space. -/
def ofOverFunctor : Over (Spec (.of (ULift.{u} ℤ))) ⥤
    AlgebraicSpace (Spec (.of (ULift.{u} ℤ))) where
  obj := ofOver
  map f := (yoneda.map f : yoneda.obj _ ⟶ yoneda.obj _)
  map_id := by intros; rfl
  map_comp := by intros; rfl

end categoryBaseChange

/-- The functor sending a scheme to itself as an object of `Sch / Spec ℤ`. -/
def baseChangeToOverSpecZ :
    Scheme.{u} ⥤ Over (Spec (.of (ULift.{u} ℤ))) where
  obj := fun T ↦ Over.mk (specULiftZIsTerminal.from T)
  map f := Over.homMk f (IsTerminal.comp_from specULiftZIsTerminal f)
  map_id := sorry
  map_comp := sorry

/-- The category of objects of `C` whose image scheme maps to an algebraic space over `Spec ℤ`.
Its objects are costructured arrows from `p ⋙ baseChangeToOverSpecZ ⋙ ofOverFunctor`. -/
abbrev categoryBaseChange {C : Type v} [Category.{w} C] (p : C ⥤ Scheme.{u})
    (B : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) :=
  CostructuredArrow
    (p ⋙ baseChangeToOverSpecZ ⋙ categoryBaseChange.ofOverFunctor) B

namespace categoryBaseChange

/-- Package an object and a morphism from its base scheme into `B` as an object of `categoryBaseChange`. -/
def mk {C : Type v} [Category.{w} C] {p : C ⥤ Scheme.{u}}
    {B : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))} (x : C)
    (h : ofOver (Over.mk (specULiftZIsTerminal.from (p.obj x))) ⟶ B) : categoryBaseChange p B :=
  CostructuredArrow.mk h

/-- A morphism in `categoryBaseChange p B` commutes with the structural maps to `B`. -/
theorem hom_spec {C : Type v} [Category.{w} C] {p : C ⥤ Scheme.{u}}
    {B : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))} {x y : categoryBaseChange p B} (α : x ⟶ y) :
    (categoryBaseChange.ofOverFunctor.map (baseChangeToOverSpecZ.map (p.map α.left)) :
      yoneda.obj _ ⟶ yoneda.obj _) ≫ y.hom = x.hom :=
  sorry

/-- The projection square for the relative category `categoryBaseChange p B`. -/
def square {C : Type v} [Category.{w} C] (p : C ⥤ Scheme.{u})
    (B : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) :
    CatCommSqOver (p ⋙ baseChangeToOverSpecZ)
      (CostructuredArrow.proj categoryBaseChange.ofOverFunctor B)
      (categoryBaseChange p B) where
  fst := CostructuredArrow.proj
    (p ⋙ baseChangeToOverSpecZ ⋙ categoryBaseChange.ofOverFunctor) B
  snd := CostructuredArrow.pre (p ⋙ baseChangeToOverSpecZ) categoryBaseChange.ofOverFunctor B
  iso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} _ ↦ rfl)

/-- The relative category is the actual categorical pullback of the two projections. -/
def comparisonEquivalence {C : Type v} [Category.{w} C] (p : C ⥤ Scheme.{u})
    (B : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) :
    categoryBaseChange p B ≌
      (p ⋙ baseChangeToOverSpecZ) ⊡ (CategoryTheory.CostructuredArrow.proj ofOverFunctor B) :=
  CategoricalPullback.CostructuredArrow.equivalence
    (p ⋙ baseChangeToOverSpecZ) ofOverFunctor B

/-- The comparison equivalence has exactly the original projection-square comparison. -/
theorem comparisonEquivalence_functor {C : Type v} [Category.{w} C] (p : C ⥤ Scheme.{u})
    (B : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) :
    (comparisonEquivalence p B).functor = (square p B).comparison := rfl

/-- The relative projection square is a resized bilimit. -/
instance instSquareIsBilimit {C : Type v} [Category.{w} C] (p : C ⥤ Scheme.{u})
    (B : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) :
    CatCommSqOver.Resized.IsBilimit (square p B) :=
  CatCommSqOver.Resized.isBilimitOfComparisonEquivalence
    (square p B) (comparisonEquivalence p B) (Iso.refl _)

end categoryBaseChange

end AlgebraicGeometry.AlgebraicSpace
