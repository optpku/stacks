/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of the forgetful strong transformation for based inertia

In a universe stable under inertia, forgetting the selected automorphism is a
strong transformation from based inertia to the identity pseudofunctor.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory.BasedCategory.Inertia

open BasedCategory BasedFunctor
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace forget.naturalityIso

/-- The objectwise naturality comparison for forgetting based inertia. Both sides send an
inertia object to the same underlying image, so the comparison is the identity isomorphism. -/
@[stacks 042H "component of based-inertia forgetful naturality"]
def component
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y)
    (A : (inertia X).obj) :
    ((pseudofunctor C).map F ⋙ forget Y).obj A ≅
      (forget X ⋙
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).map F).obj A :=
  Iso.refl _

/-- The explicit forgetful naturality components are natural in inertia morphisms. -/
@[stacks 042H "based-inertia forgetful component naturality"]
theorem component.naturality
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y)
    {A B : (inertia X).obj} (f : A ⟶ B) :
    ((pseudofunctor C).map F ⋙ forget Y).map f ≫
        (component F B).hom =
      (component F A).hom ≫
        (forget X ⋙
          (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).map F).map f := sorry

/-- The inverse explicit forgetful naturality components are natural in inertia morphisms. -/
@[reassoc, stacks 042H "based-inertia forgetful inverse component naturality"]
theorem component.invNaturality
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y)
    {A B : (inertia X).obj} (f : A ⟶ B) :
    (component F A).inv ≫
        ((pseudofunctor C).map F ⋙ forget Y).map f =
      (forget X ⋙
          (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).map F).map f ≫
        (component F B).inv := sorry

/-- Every explicit forgetful naturality component lies over the identity of the base. -/
@[stacks 042H "based-inertia forgetful component verticality"]
theorem component.isHomLift
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y)
    (A : (inertia X).obj) :
    Y.p.IsHomLift (𝟙 ((inertia X).p.obj A)) (component F A).hom := sorry

/-- Every inverse explicit forgetful naturality component lies over the identity of the base. -/
@[stacks 042H "based-inertia forgetful inverse component verticality"]
theorem component.inv.isHomLift
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y)
    (A : (inertia X).obj) :
    Y.p.IsHomLift (𝟙 ((inertia X).p.obj A)) (component F A).inv := sorry

end forget.naturalityIso

/-- The canonical naturality isomorphism for forgetting based inertia. Its objectwise arrows
are explicit identities; only naturality and verticality are proof obligations. -/
@[stacks 042H "based-inertia forgetful naturality isomorphism"]
def forget.naturalityIso
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y) :
    (pseudofunctor C).map F ⋙ forget Y ≅
      forget X ⋙
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).map F :=
  BasedNatIso.ofComponents
    (forget.naturalityIso.component F)
    (forget.naturalityIso.component.naturality F)
    (forget.naturalityIso.component.isHomLift F)

namespace Implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The forgetful component with its pseudofunctor endpoints made explicit. -/
private def forgetApp (X : BasedCategory.{vS, max w vS} C) :
    (pseudofunctor C).obj X ⟶
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).obj X :=
  forget X

/-- Naturality in source `2`-cells for based-inertia forgetting. -/
private theorem forget_naturality_naturality :
    ∀ {X Y : BasedCategory.{vS, max w vS} C} {F G : X ⟶ Y} (τ : F ⟶ G),
      (pseudofunctor C).map₂ τ ▷ forgetApp Y ≫
          (forget.naturalityIso G).hom =
        (forget.naturalityIso F).hom ≫
          forgetApp X ◁
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).map₂ τ := sorry

/-- Identity coherence for based-inertia forgetting. -/
private theorem forget_naturality_id :
    ∀ X : BasedCategory.{vS, max w vS} C,
      (forget.naturalityIso (𝟙 X)).hom ≫
          forgetApp X ◁
            ((Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).mapId X).hom =
        ((pseudofunctor C).mapId X).hom ▷ forgetApp X ≫
          (λ_ (forgetApp X)).hom ≫
          (ρ_ (forgetApp X)).inv := sorry

/-- Composition coherence for based-inertia forgetting. -/
private theorem forget_naturality_comp :
    ∀ {X Y Z : BasedCategory.{vS, max w vS} C} (F : X ⟶ Y) (G : Y ⟶ Z),
      (forget.naturalityIso (F ≫ G)).hom ≫
          forgetApp X ◁
            ((Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).mapComp F G).hom =
        ((pseudofunctor C).mapComp F G).hom ▷ forgetApp Z ≫
          (α_ _ _ _).hom ≫
          (pseudofunctor C).map F ◁
            (forget.naturalityIso G).hom ≫
          (α_ _ _ _).inv ≫
          (forget.naturalityIso F).hom ▷
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)).map G ≫
          (α_ _ _ _).hom := sorry

end Implementation

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (C) in
/-- Forgetting the selected automorphism is a strong transformation from based inertia to the
identity pseudofunctor in every universe stable under inertia. -/
@[stacks 042H "based-inertia forgetful strong transformation"]
def forget.strongTrans :
    Pseudofunctor.StrongTrans
      ((pseudofunctor C) :
        Pseudofunctor (BasedCategory.{vS, max w vS} C)
          (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)) where
  app X := Implementation.forgetApp X
  naturality F := forget.naturalityIso F
  naturality_naturality := Implementation.forget_naturality_naturality
  naturality_id := Implementation.forget_naturality_id
  naturality_comp := Implementation.forget_naturality_comp

end CategoryTheory.BasedCategory.Inertia
