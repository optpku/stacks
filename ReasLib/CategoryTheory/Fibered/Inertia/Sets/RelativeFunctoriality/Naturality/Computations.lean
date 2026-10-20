module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Naturality.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.RelativeFunctoriality.Naturality.Construction

/-!
# Set-fibred relative inertia naturality computations

This leaf exposes the based, objectwise, verticality, and underlying-arrow readouts of the
set-fibred relative-to-absolute comparison.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Sets

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace RelativeInertia

namespace toInertia

namespace naturalityIso

/-- The based projection of the forward set-fibred naturality cell is the neutral based
naturality cell. -/
@[simp]
theorem hom.toBasedNatTrans
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Sets.toBasedNatTrans
        (naturalityIso G G' comm).hom =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso
        (FiberedCategoryOver.Sets.toBasedFunctor G)
        (FiberedCategoryOver.Sets.toBasedFunctor G')
        (Bicategory.InducedBicategory.Iso.toAmbient comm)).hom := sorry

/-- The based projection of the inverse set-fibred naturality cell is the inverse neutral based
naturality cell. -/
@[simp]
theorem inv.toBasedNatTrans
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Sets.toBasedNatTrans
        (naturalityIso G G' comm).inv =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso
        (FiberedCategoryOver.Sets.toBasedFunctor G)
        (FiberedCategoryOver.Sets.toBasedFunctor G')
        (Bicategory.InducedBicategory.Iso.toAmbient comm)).inv := sorry

/-- The forward set-fibred naturality component is the explicit neutral identity-arrow
component. -/
@[simp]
theorem hom.app
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Sets.relativeInertia F₁).total) :
    (FiberedCategoryOver.Sets.toNatTrans
      (naturalityIso G G' comm).hom).app A =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso.component
        (FiberedCategoryOver.Sets.toBasedFunctor G)
        (FiberedCategoryOver.Sets.toBasedFunctor G')
        (Bicategory.InducedBicategory.Iso.toAmbient comm) A).hom := sorry

/-- The inverse set-fibred naturality component is the explicit neutral reverse identity-arrow
component. -/
@[simp]
theorem inv.app
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Sets.relativeInertia F₁).total) :
    (FiberedCategoryOver.Sets.toNatTrans
      (naturalityIso G G' comm).inv).app A =
      (BasedCategory.RelativeInertia.toInertia.naturalityIso.component
        (FiberedCategoryOver.Sets.toBasedFunctor G)
        (FiberedCategoryOver.Sets.toBasedFunctor G')
        (Bicategory.InducedBicategory.Iso.toAmbient comm) A).inv := sorry

/-- The forward set-fibred relative-to-absolute comparison is natural on total categories. -/
@[reassoc]
theorem naturality
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    {A B : (FiberedCategoryOver.Sets.relativeInertia F₁).total} (f : A ⟶ B) :
    (FiberedCategoryOver.Sets.toFunctor
        (RelativeInertia.map G G' comm ≫ toInertia F₂)).map f ≫
        (FiberedCategoryOver.Sets.toNatTrans
          (naturalityIso G G' comm).hom).app B =
      (FiberedCategoryOver.Sets.toNatTrans
          (naturalityIso G G' comm).hom).app A ≫
        (FiberedCategoryOver.Sets.toFunctor
            (toInertia F₁ ≫ (Inertia.pseudofunctor C).map G)).map f := sorry

/-- The inverse set-fibred relative-to-absolute comparison is natural on total categories. -/
@[reassoc]
theorem invNaturality
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    {A B : (FiberedCategoryOver.Sets.relativeInertia F₁).total} (f : A ⟶ B) :
    (FiberedCategoryOver.Sets.toFunctor
        (toInertia F₁ ≫ (Inertia.pseudofunctor C).map G)).map f ≫
        (FiberedCategoryOver.Sets.toNatTrans
          (naturalityIso G G' comm).inv).app B =
      (FiberedCategoryOver.Sets.toNatTrans
          (naturalityIso G G' comm).inv).app A ≫
        (FiberedCategoryOver.Sets.toFunctor
            (RelativeInertia.map G G' comm ≫ toInertia F₂)).map f := sorry

/-- Every forward set-fibred naturality component lies over the identity of the source base. -/
theorem hom.app.isHomLift
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Sets.relativeInertia F₁).total) :
    (FiberedCategoryOver.Sets.inertia X₂).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.Sets.relativeInertia F₁).p.obj A))
      ((FiberedCategoryOver.Sets.toNatTrans
        (naturalityIso G G' comm).hom).app A) := sorry

/-- Every inverse set-fibred naturality component lies over the identity of the source base. -/
theorem inv.app.isHomLift
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Sets.relativeInertia F₁).total) :
    (FiberedCategoryOver.Sets.inertia X₂).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.Sets.relativeInertia F₁).p.obj A))
      ((FiberedCategoryOver.Sets.toNatTrans
        (naturalityIso G G' comm).inv).app A) := sorry

/-- The arrow underlying every forward set-fibred naturality component is an identity. -/
@[simp]
theorem hom.app.underlying
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Sets.relativeInertia F₁).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Sets.toNatTrans
          (naturalityIso G G' comm).hom).app A) =
      𝟙 ((FiberedCategoryOver.Sets.toFunctor G).obj A.obj) := sorry

/-- The arrow underlying every inverse set-fibred naturality component is an identity. -/
@[simp]
theorem inv.app.underlying
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂')
    (comm : F₁ ≫ G' ≅ G ≫ F₂)
    (A : (FiberedCategoryOver.Sets.relativeInertia F₁).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.Sets.toNatTrans
          (naturalityIso G G' comm).inv).app A) =
      𝟙 ((FiberedCategoryOver.Sets.toFunctor G).obj A.obj) := sorry

end naturalityIso

end toInertia

end RelativeInertia

end FiberedCategoryOver.Sets

end CategoryTheory
