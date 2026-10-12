/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Naturality.Construction

/-!
# Computations for cartesian relative-inertia naturality

This module exposes the based, component, and underlying-arrow projections of the cartesian
relative-to-absolute inertia comparison.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.toInertia

variable {C : Type u} [Category.{v} C]

namespace naturalityIso

/-- Forgetting the forward cartesian naturality cell recovers the canonical based cell. -/
@[simp]
theorem hom.toBasedNatTrans
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.toBasedNatTrans
        (naturalityIso G G' comm).hom =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso
        (FiberedCategoryOver.toBasedFunctor G)
        (FiberedCategoryOver.toBasedFunctor G')
        (FiberedCategoryOver.toBasedFunctorIso comm)).hom := sorry

/-- Forgetting the inverse cartesian naturality cell recovers the canonical based cell. -/
@[simp]
theorem inv.toBasedNatTrans
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.toBasedNatTrans
        (naturalityIso G G' comm).inv =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso
        (FiberedCategoryOver.toBasedFunctor G)
        (FiberedCategoryOver.toBasedFunctor G')
        (FiberedCategoryOver.toBasedFunctorIso comm)).inv := sorry

/-- The forward cartesian naturality component is the explicit based identity-arrow component. -/
@[simp]
theorem hom.app
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.relativeInertia F₁).total) :
    (FiberedCategoryOver.toNatTrans
        (naturalityIso G G' comm).hom).app A =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso.component
        (FiberedCategoryOver.toBasedFunctor G)
        (FiberedCategoryOver.toBasedFunctor G')
        (FiberedCategoryOver.toBasedFunctorIso comm) A).hom := sorry

/-- The inverse cartesian naturality component is the explicit reverse identity-arrow component. -/
@[simp]
theorem inv.app
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.relativeInertia F₁).total) :
    (FiberedCategoryOver.toNatTrans
        (naturalityIso G G' comm).inv).app A =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso.component
        (FiberedCategoryOver.toBasedFunctor G)
        (FiberedCategoryOver.toBasedFunctor G')
        (FiberedCategoryOver.toBasedFunctorIso comm) A).inv := sorry

/- The typed bridge below keeps verticality available without requiring callers to descend to the
   based natural transformation owner. -/
/-- Every forward cartesian naturality component lies over the identity of the source base object. -/
theorem hom.app.isHomLift
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.relativeInertia F₁).total) :
    (FiberedCategoryOver.inertia X₂).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.relativeInertia F₁).p.obj A))
      ((FiberedCategoryOver.toNatTrans
        (naturalityIso G G' comm).hom).app A) := sorry

/-- Every inverse cartesian naturality component lies over the identity of the source base object. -/
theorem inv.app.isHomLift
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.relativeInertia F₁).total) :
    (FiberedCategoryOver.inertia X₂).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.relativeInertia F₁).p.obj A))
      ((FiberedCategoryOver.toNatTrans
        (naturalityIso G G' comm).inv).app A) := sorry

/-- The forward cartesian relative-to-absolute comparison is natural on total categories. -/
@[reassoc]
theorem naturality
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    {A B : (FiberedCategoryOver.relativeInertia F₁).total} (f : A ⟶ B) :
    (FiberedCategoryOver.toFunctor
        (FiberedCategoryOver.RelativeInertia.map G G' comm ≫
          FiberedCategoryOver.RelativeInertia.toInertia F₂)).map f ≫
        (FiberedCategoryOver.toNatTrans
          (naturalityIso G G' comm).hom).app B =
      (FiberedCategoryOver.toNatTrans
          (naturalityIso G G' comm).hom).app A ≫
        (FiberedCategoryOver.toFunctor
            (FiberedCategoryOver.RelativeInertia.toInertia F₁ ≫
              FiberedCategoryOver.Inertia.map G)).map f := sorry

/-- The inverse cartesian relative-to-absolute comparison is natural on total categories. -/
@[reassoc]
theorem invNaturality
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    {A B : (FiberedCategoryOver.relativeInertia F₁).total} (f : A ⟶ B) :
    (FiberedCategoryOver.toFunctor
        (FiberedCategoryOver.RelativeInertia.toInertia F₁ ≫
          FiberedCategoryOver.Inertia.map G)).map f ≫
        (FiberedCategoryOver.toNatTrans
          (naturalityIso G G' comm).inv).app B =
      (FiberedCategoryOver.toNatTrans
          (naturalityIso G G' comm).inv).app A ≫
        (FiberedCategoryOver.toFunctor
            (FiberedCategoryOver.RelativeInertia.map G G' comm ≫
              FiberedCategoryOver.RelativeInertia.toInertia F₂)).map f := sorry

/-- The arrow underlying each forward cartesian naturality component is an identity. -/
@[simp]
theorem hom.app.underlying
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.relativeInertia F₁).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          (naturalityIso G G' comm).hom).app A) =
      𝟙 ((FiberedCategoryOver.toFunctor G).obj A.obj) := sorry

/-- The arrow underlying each inverse cartesian naturality component is an identity. -/
@[simp]
theorem inv.app.underlying
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.relativeInertia F₁).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          (naturalityIso G G' comm).inv).app A) =
      𝟙 ((FiberedCategoryOver.toFunctor G).obj A.obj) := sorry

end naturalityIso

end FiberedCategoryOver.RelativeInertia.toInertia

end CategoryTheory
