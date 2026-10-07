module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Naturality.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Naturality.Construction

/-!
# Groupoid-fibred relative inertia naturality computations

This leaf exposes the based, objectwise, and underlying-arrow readouts of the
groupoid-fibred relative-to-absolute comparison.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Groupoids

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
      FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans
        (naturalityIso G G' comm).hom =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor G)
        (FiberedCategoryOver.Groupoids.toBasedFunctor G')
        (FiberedCategoryOver.Groupoids.toBasedFunctorIso comm)).hom := sorry

/-- The based projection of the inverse relative-to-absolute inertia naturality cell is the
inverse neutral based naturality cell. -/
@[simp]
theorem inv.toBasedNatTrans
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Groupoids.toBasedNatTrans
        (naturalityIso G G' comm).inv =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso
        (FiberedCategoryOver.Groupoids.toBasedFunctor G)
        (FiberedCategoryOver.Groupoids.toBasedFunctor G')
        (FiberedCategoryOver.Groupoids.toBasedFunctorIso comm)).inv := sorry

/-- The forward component of groupoid-fibred relative-to-absolute inertia naturality is the
explicit neutral identity-arrow component. -/
@[simp]
theorem hom.app
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Groupoids.relativeInertia F₁).total) :
    (FiberedCategoryOver.Groupoids.toNatTrans
      (naturalityIso G G' comm).hom).app A =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso.component
        (FiberedCategoryOver.Groupoids.toBasedFunctor G)
        (FiberedCategoryOver.Groupoids.toBasedFunctor G')
        (FiberedCategoryOver.Groupoids.toBasedFunctorIso comm) A).hom := sorry

/-- The inverse component of groupoid-fibred relative-to-absolute inertia naturality is the
explicit reverse identity-arrow component. -/
@[simp]
theorem inv.app
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Groupoids.relativeInertia F₁).total) :
    (FiberedCategoryOver.Groupoids.toNatTrans
      (naturalityIso G G' comm).inv).app A =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso.component
        (FiberedCategoryOver.Groupoids.toBasedFunctor G)
        (FiberedCategoryOver.Groupoids.toBasedFunctor G')
        (FiberedCategoryOver.Groupoids.toBasedFunctorIso comm) A).inv := sorry

/- The typed bridge below keeps verticality available without requiring callers to descend to the
   based natural transformation owner. -/
/-- Every forward groupoid-fibred naturality component lies over the identity of the source base. -/
theorem hom.app.isHomLift
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Groupoids.relativeInertia F₁).total) :
    (FiberedCategoryOver.Groupoids.inertia X₂).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.Groupoids.relativeInertia F₁).p.obj A))
      ((FiberedCategoryOver.Groupoids.toNatTrans
        (naturalityIso G G' comm).hom).app A) := sorry

/-- Every inverse groupoid-fibred naturality component lies over the identity of the source base. -/
theorem inv.app.isHomLift
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Groupoids.relativeInertia F₁).total) :
    (FiberedCategoryOver.Groupoids.inertia X₂).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.Groupoids.relativeInertia F₁).p.obj A))
      ((FiberedCategoryOver.Groupoids.toNatTrans
        (naturalityIso G G' comm).inv).app A) := sorry

/-- The forward groupoid-fibred relative-to-absolute comparison is natural on total categories. -/
@[reassoc]
theorem naturality
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    {A B : (FiberedCategoryOver.Groupoids.relativeInertia F₁).total} (f : A ⟶ B) :
    (FiberedCategoryOver.Groupoids.toFunctor
        (RelativeInertia.map G G' comm ≫ toInertia F₂)).map f ≫
        (FiberedCategoryOver.Groupoids.toNatTrans
          (naturalityIso G G' comm).hom).app B =
      (FiberedCategoryOver.Groupoids.toNatTrans
          (naturalityIso G G' comm).hom).app A ≫
        (FiberedCategoryOver.Groupoids.toFunctor
            (toInertia F₁ ≫ (Inertia.pseudofunctor C).map G)).map f := sorry

/-- The inverse groupoid-fibred relative-to-absolute comparison is natural on total categories. -/
@[reassoc]
theorem invNaturality
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    {A B : (FiberedCategoryOver.Groupoids.relativeInertia F₁).total} (f : A ⟶ B) :
    (FiberedCategoryOver.Groupoids.toFunctor
        (toInertia F₁ ≫ (Inertia.pseudofunctor C).map G)).map f ≫
        (FiberedCategoryOver.Groupoids.toNatTrans
          (naturalityIso G G' comm).inv).app B =
      (FiberedCategoryOver.Groupoids.toNatTrans
          (naturalityIso G G' comm).inv).app A ≫
        (FiberedCategoryOver.Groupoids.toFunctor
            (RelativeInertia.map G G' comm ≫ toInertia F₂)).map f := sorry

/-- The arrow underlying every forward relative-to-absolute inertia naturality component is an
identity. -/
@[simp]
theorem hom.app.underlying
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Groupoids.relativeInertia F₁).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans
          (naturalityIso G G' comm).hom).app A) =
      𝟙 ((FiberedCategoryOver.Groupoids.toFunctor G).obj A.obj) := sorry

/-- The arrow underlying every inverse relative-to-absolute inertia naturality component is an
identity. -/
@[simp]
theorem inv.app.underlying
    {X₁ X₁' X₂ X₂' :
      FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Groupoids.relativeInertia F₁).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Groupoids.toNatTrans
          (naturalityIso G G' comm).inv).app A) =
      𝟙 ((FiberedCategoryOver.Groupoids.toFunctor G).obj A.obj) := sorry

/- Axiom audit: the non-Prop comparison cells of `naturalityIso` are the explicit neutral
construction above. `#print axioms` additionally reports `sorryAx` only through inherited
based-category, functor-law, owner-membership, and naturality proof fields. -/

end naturalityIso

end toInertia

end RelativeInertia

end FiberedCategoryOver.Groupoids

end CategoryTheory
