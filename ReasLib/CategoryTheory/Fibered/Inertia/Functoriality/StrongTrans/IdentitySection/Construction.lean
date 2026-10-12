/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of the identity-section strong transformation

This module owns the concrete naturality comparison and coherence data.  Component
computations live in `IdentitySection.Computations`.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory.BasedCategory.Inertia

open BasedCategory BasedFunctor
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace identitySection.naturalityIso

/-- The identity arrow intertwines the two neutral automorphisms occurring in identity-section
naturality. -/
@[stacks 04Z3 "based-inertia identity-section component compatibility"]
theorem component.comm
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y) (x : X.obj) :
    (((Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).map F ⋙
          identitySection Y).obj x).aut.hom ≫ 𝟙 _ =
      𝟙 _ ≫
        ((identitySection X ⋙ (pseudofunctor C).map F).obj x).aut.hom := sorry

/-- The objectwise identity-section naturality comparison has identity underlying arrow. -/
@[stacks 04Z3 "component of based-inertia identity-section naturality"]
def component
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y) (x : X.obj) :
    ((Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).map F ⋙
        identitySection Y).obj x ≅
      (identitySection X ⋙ (pseudofunctor C).map F).obj x :=
  CategoryTheory.RelativeInertia.isoMk Y.p (Iso.refl _)
    (component.comm F x)

/-- The explicit identity-section naturality components are natural in source morphisms. -/
@[stacks 04Z3 "based-inertia identity-section component naturality"]
theorem component.naturality
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y)
    {x y : X.obj} (f : x ⟶ y) :
    ((Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).map F ⋙
        identitySection Y).map f ≫ (component F y).hom =
      (component F x).hom ≫
        (identitySection X ⋙ (pseudofunctor C).map F).map f := sorry

/-- The inverse explicit identity-section naturality components are natural in source morphisms. -/
@[reassoc, stacks 04Z3 "based-inertia identity-section inverse component naturality"]
theorem component.invNaturality
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y)
    {x y : X.obj} (f : x ⟶ y) :
    (component F x).inv ≫
        ((Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).map F ⋙
          identitySection Y).map f =
      (identitySection X ⋙ (pseudofunctor C).map F).map f ≫
        (component F y).inv := sorry

/-- Every explicit identity-section naturality component lies over the identity of the base. -/
@[stacks 04Z3 "based-inertia identity-section component verticality"]
theorem component.isHomLift
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y) (x : X.obj) :
    (inertia Y).p.IsHomLift (𝟙 (X.p.obj x)) (component F x).hom := sorry

/-- Every inverse explicit identity-section naturality component lies over the identity of the
base. -/
@[stacks 04Z3 "based-inertia identity-section inverse component verticality"]
theorem component.inv.isHomLift
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y) (x : X.obj) :
    (inertia Y).p.IsHomLift (𝟙 (X.p.obj x)) (component F x).inv := sorry

end identitySection.naturalityIso

/-- The canonical naturality isomorphism for the neutral identity section. Its components are
relative-inertia isomorphisms with identity underlying arrows. -/
@[stacks 04Z3 "based-inertia identity-section naturality isomorphism"]
def identitySection.naturalityIso
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y) :
    (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).map F ⋙
        identitySection Y ≅
      identitySection X ⋙ (pseudofunctor C).map F :=
  BasedNatIso.ofComponents
    (identitySection.naturalityIso.component F)
    (identitySection.naturalityIso.component.naturality F)
    (identitySection.naturalityIso.component.isHomLift F)

namespace Implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The identity-section component with its pseudofunctor endpoints made explicit. -/
private def sectionApp (X : BasedCategory.{vS, max w vS} C) :
    (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).obj X ⟶
      (pseudofunctor C).obj X :=
  identitySection X

/-- Naturality in source `2`-cells for the based-inertia identity section. -/
private theorem section_naturality_naturality :
    ∀ {X Y : BasedCategory.{vS, max w vS} C} {F G : X ⟶ Y} (τ : F ⟶ G),
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).map₂ τ ▷
            sectionApp Y ≫
          (identitySection.naturalityIso G).hom =
        (identitySection.naturalityIso F).hom ≫
          sectionApp X ◁ (pseudofunctor C).map₂ τ := sorry

/-- Identity coherence for the based-inertia identity section. -/
private theorem section_naturality_id :
    ∀ X : BasedCategory.{vS, max w vS} C,
      (identitySection.naturalityIso (𝟭 X)).hom ≫
          sectionApp X ◁ ((pseudofunctor C).mapId X).hom =
        ((Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).mapId X).hom ▷
            sectionApp X ≫
          (λ_ (sectionApp X)).hom ≫
          (ρ_ (sectionApp X)).inv := sorry

/-- Composition coherence for the based-inertia identity section. -/
private theorem section_naturality_comp :
    ∀ {X Y Z : BasedCategory.{vS, max w vS} C} (F : X ⟶ Y) (G : Y ⟶ Z),
      (identitySection.naturalityIso (F ≫ G)).hom ≫
          sectionApp X ◁ ((pseudofunctor C).mapComp F G).hom =
        ((Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).mapComp F G).hom ▷
            sectionApp Z ≫
          (α_ _ _ _).hom ≫
          (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).map F ◁
            (identitySection.naturalityIso G).hom ≫
          (α_ _ _ _).inv ≫
          (identitySection.naturalityIso F).hom ▷
            (pseudofunctor C).map G ≫
          (α_ _ _ _).hom := sorry

end Implementation

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (C) in
/-- Inserting the identity automorphism is a strong transformation from the identity
pseudofunctor to based inertia in every universe stable under inertia. -/
@[stacks 04Z3 "based-inertia identity-section strong transformation"]
def identitySection.strongTrans :
    Pseudofunctor.StrongTrans
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      ((pseudofunctor C) :
        Pseudofunctor (BasedCategory.{vS, max w vS} C)
          (BasedCategory.{vS, max w vS} C)) where
  app X := Implementation.sectionApp X
  naturality F := identitySection.naturalityIso F
  naturality_naturality := Implementation.section_naturality_naturality
  naturality_id := Implementation.section_naturality_id
  naturality_comp := Implementation.section_naturality_comp

end CategoryTheory.BasedCategory.Inertia
