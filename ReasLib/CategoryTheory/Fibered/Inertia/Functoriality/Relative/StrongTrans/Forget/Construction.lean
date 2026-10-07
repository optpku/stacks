module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Pseudofunctor.Construction
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of the pseudo-comma relative-inertia forgetful transformation

In a universe stable under relative inertia, the forgetful based functors assemble into a
strong transformation from pseudo-comma relative inertia to the left-endpoint pseudofunctor.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory
namespace BasedCategory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

noncomputable section

namespace RelativeInertia
namespace pseudoComma

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))}

namespace forget.naturalityIso

/-- The objectwise comparison for forgetting the relative automorphism is the identity arrow on
the left endpoint of a pseudo-comma object. -/
@[stacks 042H "relative-inertia forgetful component"]
def component (f : S ⟶ T) (A : ((pseudofunctor C).obj S).obj) :
    ((pseudofunctor C).map f ≫ RelativeInertia.forget T.hom).obj A ≅
      (RelativeInertia.forget S.hom ≫
        (Bicategory.PseudoComma.fst
          (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
          (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).map f).obj A :=
  Iso.refl _

/-- The identity comparison is natural in morphisms of relative-inertia objects. -/
@[stacks 042H "relative-inertia forgetful component naturality"]
theorem component.naturality (f : S ⟶ T)
    {A B : ((pseudofunctor C).obj S).obj} (φ : A ⟶ B) :
    ((pseudofunctor C).map f ≫ RelativeInertia.forget T.hom).map φ ≫
        (component f B).hom =
      (component f A).hom ≫
        (RelativeInertia.forget S.hom ≫
          (Bicategory.PseudoComma.fst
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).map f).map φ := sorry

/-- The inverse pseudo-comma forgetful comparison components are natural in relative-inertia
morphisms. -/
@[reassoc, stacks 042H "relative-inertia forgetful inverse component naturality"]
theorem component.invNaturality (f : S ⟶ T)
    {A B : ((pseudofunctor C).obj S).obj} (φ : A ⟶ B) :
    (component f A).inv ≫
        ((pseudofunctor C).map f ≫ RelativeInertia.forget T.hom).map φ =
      (RelativeInertia.forget S.hom ≫
          (Bicategory.PseudoComma.fst
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).map f).map φ ≫
        (component f B).inv := sorry

/-- The objectwise forgetful comparison is vertical over the pseudo-comma base. -/
@[stacks 042H "relative-inertia forgetful component verticality"]
theorem component.isHomLift (f : S ⟶ T)
    (A : ((pseudofunctor C).obj S).obj) :
    ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj T).p.IsHomLift
      (𝟙 ((pseudofunctor C).obj S).p.obj A) (component f A).hom := sorry

/-- Every inverse pseudo-comma forgetful comparison component is vertical over the identity base
arrow. -/
@[stacks 042H "relative-inertia forgetful inverse component verticality"]
theorem component.inv.isHomLift (f : S ⟶ T)
    (A : ((pseudofunctor C).obj S).obj) :
    ((Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj T).p.IsHomLift
      (𝟙 ((pseudofunctor C).obj S).p.obj A) (component f A).inv := sorry

end forget.naturalityIso

/-- The forgetful naturality isomorphism for a pseudo-comma square. -/
@[stacks 042H "relative-inertia forgetful naturality isomorphism"]
def forget.naturalityIso (f : S ⟶ T) :
    (pseudofunctor C).map f ≫ RelativeInertia.forget T.hom ≅
      RelativeInertia.forget S.hom ≫
        (Bicategory.PseudoComma.fst
          (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
          (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).map f :=
  BasedNatIso.ofComponents
    (forget.naturalityIso.component f)
    (forget.naturalityIso.component.naturality f)
    (forget.naturalityIso.component.isHomLift f)

namespace forget.Implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The forgetful component with its relative-inertia pseudofunctor endpoint explicit. -/
private def forgetApp
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))) :
    (pseudofunctor C).obj S ⟶
      (Bicategory.PseudoComma.fst
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S :=
  RelativeInertia.forget S.hom

/-- Naturality of relative-inertia forgetting on pseudo-comma `2`-cells. -/
private theorem naturality_naturality
    {f g : S ⟶ T} (η : f ⟶ g) :
    (pseudofunctor C).map₂ η ▷ forgetApp T ≫
        (forget.naturalityIso g).hom =
      (forget.naturalityIso f).hom ≫
        forgetApp S ◁
          (Bicategory.PseudoComma.fst
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).map₂ η := sorry

/-- Identity coherence for relative-inertia forgetting on the pseudo-comma bicategory. -/
private theorem naturality_id
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))) :
    (forget.naturalityIso (𝟙 S)).hom ≫
        forgetApp S ◁
          ((Bicategory.PseudoComma.fst
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).mapId S).hom =
      ((pseudofunctor C).mapId S).hom ▷ forgetApp S ≫
        (λ_ (forgetApp S)).hom ≫
        (ρ_ (forgetApp S)).inv := sorry

/-- Composition coherence for relative-inertia forgetting on the pseudo-comma bicategory. -/
private theorem naturality_comp
    {R S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))}
    (f : R ⟶ S) (g : S ⟶ T) :
    (forget.naturalityIso (f ≫ g)).hom ≫
        forgetApp R ◁
          ((Bicategory.PseudoComma.fst
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).mapComp f g).hom =
      ((pseudofunctor C).mapComp f g).hom ▷ forgetApp T ≫
        (α_ _ _ _).hom ≫
        (pseudofunctor C).map f ◁ (forget.naturalityIso g).hom ≫
        (α_ _ _ _).inv ≫
        (forget.naturalityIso f).hom ▷
          (Bicategory.PseudoComma.fst
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).map g ≫
        (α_ _ _ _).hom := sorry

end forget.Implementation

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (C) in
/-- Forgetting the relative automorphism is a strong transformation from the relative-inertia
pseudofunctor to the left-endpoint pseudo-comma pseudofunctor. -/
@[stacks 042H "relative-inertia forgetful strong transformation"]
def forget.strongTrans :
    Pseudofunctor.StrongTrans
      ((pseudofunctor C) :
        Pseudofunctor
          (Bicategory.PseudoComma
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)))
          (BasedCategory.{vS, max w vS} C))
      (Bicategory.PseudoComma.fst
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))) where
  app S := forget.Implementation.forgetApp S
  naturality f := forget.naturalityIso f
  naturality_naturality := forget.Implementation.naturality_naturality
  naturality_id := forget.Implementation.naturality_id
  naturality_comp := forget.Implementation.naturality_comp

end pseudoComma
end RelativeInertia

end

end BasedCategory
end CategoryTheory
