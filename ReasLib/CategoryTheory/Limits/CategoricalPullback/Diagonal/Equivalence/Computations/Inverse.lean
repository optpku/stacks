module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Equivalence

/-!
# Inverse computations for the categorical-pullback diagonal equivalence

This leaf exposes the object, morphism, and projection-isomorphism components of the explicit
inverse.  Downstream calculations can therefore use the canonical inverse without unfolding its
private assembly.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory.Limits

universe vA vB vC vD uA uB uC uD

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace CategoricalPullback.DiagonalComparison.equivalence

variable (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)

/-- The first object of the explicit inverse is the first object of the inner pullback. -/
@[simp] theorem inverse.obj.fst
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    ((DiagonalComparison.equivalence F G H).inverse.obj X).fst = X.fst.fst := sorry

/-- The second object of the explicit inverse is the second object of the inner pullback. -/
@[simp] theorem inverse.obj.snd
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    ((DiagonalComparison.equivalence F G H).inverse.obj X).snd = X.fst.snd := sorry

/-- The structural isomorphism of the explicit inverse is recovered from the two projections of
the outer pullback isomorphism. -/
@[simp] theorem inverse.obj.iso
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    ((DiagonalComparison.equivalence F G H).inverse.obj X).iso =
      (π₁ H H).mapIso X.iso ≪≫ ((π₂ H H).mapIso X.iso).symm := sorry

/-- The first map of the explicit inverse is the first inner map. -/
@[simp] theorem inverse.map.fst
    {X Y : (toDiagonal F G H) ⊡ (Δₚ H)} (f : X ⟶ Y) :
    ((DiagonalComparison.equivalence F G H).inverse.map f).fst = f.fst.fst := sorry

/-- The second map of the explicit inverse is the second inner map. -/
@[simp] theorem inverse.map.snd
    {X Y : (toDiagonal F G H) ⊡ (Δₚ H)} (f : X ⟶ Y) :
    ((DiagonalComparison.equivalence F G H).inverse.map f).snd = f.fst.snd := sorry

end CategoricalPullback.DiagonalComparison.equivalence

namespace CategoricalPullback.DiagonalComparison

/-- The forward component of the inverse first-projection comparison is the identity. -/
@[simp] theorem inverseFstIso.hom.app
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    (inverseFstIso F G H).hom.app X = 𝟙 _ := sorry

/-- The inverse component of the inverse first-projection comparison is the identity. -/
@[simp] theorem inverseFstIso.inv.app
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    (inverseFstIso F G H).inv.app X = 𝟙 _ := sorry

/-- The forward component of the inverse second-projection comparison is the identity. -/
@[simp] theorem inverseSndIso.hom.app
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    (inverseSndIso F G H).hom.app X = 𝟙 _ := sorry

/-- The inverse component of the inverse second-projection comparison is the identity. -/
@[simp] theorem inverseSndIso.inv.app
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    (inverseSndIso F G H).inv.app X = 𝟙 _ := sorry

end CategoricalPullback.DiagonalComparison

end CategoryTheory.Limits
