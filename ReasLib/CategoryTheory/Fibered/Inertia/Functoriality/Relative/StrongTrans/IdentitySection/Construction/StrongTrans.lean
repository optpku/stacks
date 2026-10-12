/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.StrongTrans.IdentitySection.Construction.Component
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

import Mathlib.Tactic.CrossRefAttribute

/-!
# Strong-transformation coherence for the pseudo-comma identity section

The component and naturality data are public and owned by `Construction.Component`.  This leaf
keeps the `StrongTrans` coherence witnesses private while exporting the bundled transformation.
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

namespace identitySection.Implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The identity-section component with both pseudofunctor endpoints explicit. -/
private def sectionApp
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))) :
    (Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).obj S ⟶
        (pseudofunctor C).obj S :=
  RelativeInertia.identitySection S.hom

/-- Naturality of the neutral section on pseudo-comma `2`-cells. -/
private theorem naturality_naturality
    {f g : S ⟶ T} (η : f ⟶ g) :
    (Bicategory.PseudoComma.fst
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).map₂ η ▷ sectionApp T ≫
        (identitySection.naturalityIso g).hom =
      (identitySection.naturalityIso f).hom ≫
        sectionApp S ◁ (pseudofunctor C).map₂ η := sorry

/-- Identity coherence for the neutral section on the pseudo-comma bicategory. -/
private theorem naturality_id
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))) :
    (identitySection.naturalityIso (𝟙 S)).hom ≫
        sectionApp S ◁ ((pseudofunctor C).mapId S).hom =
      ((Bicategory.PseudoComma.fst
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).mapId S).hom ▷
          sectionApp S ≫
        (λ_ (sectionApp S)).hom ≫ (ρ_ (sectionApp S)).inv := sorry

/-- Composition coherence for the neutral section on the pseudo-comma bicategory. -/
private theorem naturality_comp
    {R S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
      (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))}
    (f : R ⟶ S) (g : S ⟶ T) :
    (identitySection.naturalityIso (f ≫ g)).hom ≫
        sectionApp R ◁ ((pseudofunctor C).mapComp f g).hom =
      ((Bicategory.PseudoComma.fst
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).mapComp f g).hom ▷
          sectionApp T ≫
        (α_ _ _ _).hom ≫
        (Bicategory.PseudoComma.fst
          (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
          (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))).map f ◁
            (identitySection.naturalityIso g).hom ≫
        (α_ _ _ _).inv ≫
        (identitySection.naturalityIso f).hom ▷ (pseudofunctor C).map g ≫
        (α_ _ _ _).hom := sorry

end identitySection.Implementation

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (C) in
/-- Inserting the identity automorphism is a strong transformation from the left-endpoint
pseudo-comma pseudofunctor to relative inertia. -/
@[stacks 04Z3 "relative-inertia identity-section strong transformation"]
def identitySection.strongTrans :
    Pseudofunctor.StrongTrans
      (Bicategory.PseudoComma.fst
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
        (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)))
      ((pseudofunctor C) :
        Pseudofunctor
          (Bicategory.PseudoComma
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C))
            (Pseudofunctor.id (BasedCategory.{vS, max w vS} C)))
          (BasedCategory.{vS, max w vS} C)) where
  app S := identitySection.Implementation.sectionApp S
  naturality f := identitySection.naturalityIso f
  naturality_naturality := identitySection.Implementation.naturality_naturality
  naturality_id := identitySection.Implementation.naturality_id
  naturality_comp := identitySection.Implementation.naturality_comp

end pseudoComma
end RelativeInertia

end

end BasedCategory
end CategoryTheory
