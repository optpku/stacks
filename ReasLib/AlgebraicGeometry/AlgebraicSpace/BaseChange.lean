module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Resize

/-!
# Base change of categories over schemes to an algebraic-space base

For a category equipped with a functor to schemes, this file constructs the category of
objects whose base scheme maps to the algebraic space over `Spec ℤ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoricalPullback

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

namespace baseChange

/-- The functor sending a scheme over `Spec ℤ` to its representable algebraic space. -/
def ofOverFunctor : Over (Spec (.of (ULift.{u} ℤ))) ⥤
    AlgebraicSpace (Spec (.of (ULift.{u} ℤ))) where
  obj := ofOver
  map f := (yoneda.map f : yoneda.obj _ ⟶ yoneda.obj _)
  map_id := by intros; rfl
  map_comp := by intros; rfl

end baseChange

/-- The functor sending a scheme to itself as an object of `Sch / Spec ℤ`. -/
def baseChangeToOverSpecZ :
    Scheme.{u} ⥤ Over (Spec (.of (ULift.{u} ℤ))) where
  obj := fun T ↦ Over.mk (specULiftZIsTerminal.from T)
  map f := Over.homMk f (IsTerminal.comp_from specULiftZIsTerminal f)
  map_id := sorry
  map_comp := sorry

/-- The category of objects of `C` whose image scheme maps to an algebraic space over `Spec ℤ`.
Its objects are costructured arrows from `p ⋙ baseChangeToOverSpecZ ⋙ ofOverFunctor`. -/
abbrev baseChange {C : Type v} [Category.{w} C] (p : C ⥤ Scheme.{u})
    (B : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) :=
  CostructuredArrow
    (p ⋙ baseChangeToOverSpecZ ⋙ baseChange.ofOverFunctor) B

namespace baseChange

/-- Package an object and a morphism from its base scheme into `B` as an object of `baseChange`. -/
def mk {C : Type v} [Category.{w} C] {p : C ⥤ Scheme.{u}}
    {B : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))} (x : C)
    (h : ofOver (Over.mk (specULiftZIsTerminal.from (p.obj x))) ⟶ B) : baseChange p B :=
  CostructuredArrow.mk h

/-- A morphism in `baseChange p B` commutes with the structural maps to `B`. -/
theorem hom_spec {C : Type v} [Category.{w} C] {p : C ⥤ Scheme.{u}}
    {B : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))} {x y : baseChange p B} (α : x ⟶ y) :
    (baseChange.ofOverFunctor.map (baseChangeToOverSpecZ.map (p.map α.left)) :
      yoneda.obj _ ⟶ yoneda.obj _) ≫ y.hom = x.hom :=
  sorry

/-- The projection square for the relative category `baseChange p B`. -/
def square {C : Type v} [Category.{w} C] (p : C ⥤ Scheme.{u})
    (B : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) :
    CatCommSqOver (p ⋙ baseChangeToOverSpecZ)
      (CostructuredArrow.proj baseChange.ofOverFunctor B)
      (baseChange p B) where
  fst := CostructuredArrow.proj
    (p ⋙ baseChangeToOverSpecZ ⋙ baseChange.ofOverFunctor) B
  snd := CostructuredArrow.pre (p ⋙ baseChangeToOverSpecZ) baseChange.ofOverFunctor B
  iso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} _ ↦ rfl)

/-- The relative projection square is a resized bilimit. -/
instance instSquareIsBilimit {C : Type v} [Category.{w} C] (p : C ⥤ Scheme.{u})
    (B : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) :
    CatCommSqOver.Resized.IsBilimit (square p B) :=
  sorry

end baseChange

end AlgebraicGeometry.AlgebraicSpace
