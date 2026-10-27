/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Naturality.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.RelativeFunctoriality.Naturality.Construction

/-!
# Setoid-fibred relative inertia naturality computations

This leaf exposes the based, objectwise, and underlying-arrow readouts of the
setoid-fibred relative-to-absolute comparison.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Setoids

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace RelativeInertia

namespace toInertia

namespace naturalityIso

/-- The based projection of the forward relative-to-absolute inertia naturality cell is the
neutral based naturality cell. -/
@[simp]
theorem hom.toBasedNatTrans
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Setoids.toBasedNatTrans
        (naturalityIso G G' comm).hom =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso
        (FiberedCategoryOver.Setoids.toBasedFunctor G)
        (FiberedCategoryOver.Setoids.toBasedFunctor G')
        (FiberedCategoryOver.Setoids.toBasedFunctorIso comm)).hom := by
  rfl

/-- The based projection of the inverse relative-to-absolute inertia naturality cell is the
inverse neutral based naturality cell. -/
@[simp]
theorem inv.toBasedNatTrans
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Setoids.toBasedNatTrans
        (naturalityIso G G' comm).inv =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso
        (FiberedCategoryOver.Setoids.toBasedFunctor G)
        (FiberedCategoryOver.Setoids.toBasedFunctor G')
        (FiberedCategoryOver.Setoids.toBasedFunctorIso comm)).inv := by
  rfl

/-- The forward component of setoid-fibred relative-to-absolute inertia naturality is the
explicit neutral identity-arrow component. -/
@[simp]
theorem hom.app
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Setoids.relativeInertia F₁).total) :
    (FiberedCategoryOver.Setoids.toNatTrans
      (naturalityIso G G' comm).hom).app A =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso.component
        (FiberedCategoryOver.Setoids.toBasedFunctor G)
        (FiberedCategoryOver.Setoids.toBasedFunctor G')
        (FiberedCategoryOver.Setoids.toBasedFunctorIso comm) A).hom := by
  rfl

/-- The inverse component of setoid-fibred relative-to-absolute inertia naturality is the
explicit reverse identity-arrow component. -/
@[simp]
theorem inv.app
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Setoids.relativeInertia F₁).total) :
    (FiberedCategoryOver.Setoids.toNatTrans
      (naturalityIso G G' comm).inv).app A =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso.component
        (FiberedCategoryOver.Setoids.toBasedFunctor G)
        (FiberedCategoryOver.Setoids.toBasedFunctor G')
        (FiberedCategoryOver.Setoids.toBasedFunctorIso comm) A).inv := by
  rfl

/- The typed bridge below keeps verticality available without requiring callers to descend to the
   based natural transformation owner. -/
/-- Every forward setoid-fibred naturality component lies over the identity of the source base. -/
theorem hom.app.isHomLift
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Setoids.relativeInertia F₁).total) :
    (FiberedCategoryOver.Setoids.inertia X₂).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.Setoids.relativeInertia F₁).p.obj A))
      ((FiberedCategoryOver.Setoids.toNatTrans
        (naturalityIso G G' comm).hom).app A) := by
  exact (FiberedCategoryOver.Setoids.toBasedNatTrans
    (naturalityIso G G' comm).hom).isHomLift' A

/-- Every inverse setoid-fibred naturality component lies over the identity of the source base. -/
theorem inv.app.isHomLift
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Setoids.relativeInertia F₁).total) :
    (FiberedCategoryOver.Setoids.inertia X₂).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.Setoids.relativeInertia F₁).p.obj A))
      ((FiberedCategoryOver.Setoids.toNatTrans
        (naturalityIso G G' comm).inv).app A) := by
  exact (FiberedCategoryOver.Setoids.toBasedNatTrans
    (naturalityIso G G' comm).inv).isHomLift' A

/-- The forward setoid-fibred relative-to-absolute comparison is natural on total categories. -/
@[reassoc]
theorem naturality
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    {A B : (FiberedCategoryOver.Setoids.relativeInertia F₁).total} (f : A ⟶ B) :
    (FiberedCategoryOver.Setoids.toFunctor
        (RelativeInertia.map G G' comm ≫ toInertia F₂)).map f ≫
        (FiberedCategoryOver.Setoids.toNatTrans
          (naturalityIso G G' comm).hom).app B =
      (FiberedCategoryOver.Setoids.toNatTrans
          (naturalityIso G G' comm).hom).app A ≫
        (FiberedCategoryOver.Setoids.toFunctor
            (toInertia F₁ ≫ (Inertia.pseudofunctor C).map G)).map f := by
  exact (FiberedCategoryOver.Setoids.toNatTrans
    (naturalityIso G G' comm).hom).naturality f

/-- The inverse setoid-fibred relative-to-absolute comparison is natural on total categories. -/
@[reassoc]
theorem invNaturality
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    {A B : (FiberedCategoryOver.Setoids.relativeInertia F₁).total} (f : A ⟶ B) :
    (FiberedCategoryOver.Setoids.toFunctor
        (toInertia F₁ ≫ (Inertia.pseudofunctor C).map G)).map f ≫
        (FiberedCategoryOver.Setoids.toNatTrans
          (naturalityIso G G' comm).inv).app B =
      (FiberedCategoryOver.Setoids.toNatTrans
          (naturalityIso G G' comm).inv).app A ≫
        (FiberedCategoryOver.Setoids.toFunctor
            (RelativeInertia.map G G' comm ≫ toInertia F₂)).map f := by
  exact (FiberedCategoryOver.Setoids.toNatTrans
    (naturalityIso G G' comm).inv).naturality f

/-- The arrow underlying every forward relative-to-absolute inertia naturality component is an
identity. -/
@[simp]
theorem hom.app.underlying
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Setoids.relativeInertia F₁).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toNatTrans
          (naturalityIso G G' comm).hom).app A) =
      𝟙 ((FiberedCategoryOver.Setoids.toFunctor G).obj A.obj) := by
  rfl

/-- The arrow underlying every inverse relative-to-absolute inertia naturality component is an
identity. -/
@[simp]
theorem inv.app.underlying
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Setoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Setoids.relativeInertia F₁).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Setoids.toNatTrans
          (naturalityIso G G' comm).inv).app A) =
      𝟙 ((FiberedCategoryOver.Setoids.toFunctor G).obj A.obj) := by
  rfl

/- Axiom audit: the non-Prop comparison cells of `naturalityIso` are the explicit neutral
construction above. `#print axioms` additionally reports `sorryAx` only through inherited
based-category, functor-law, owner-membership, and naturality proof fields. -/

end naturalityIso

end toInertia

end RelativeInertia

end FiberedCategoryOver.Setoids

end CategoryTheory
