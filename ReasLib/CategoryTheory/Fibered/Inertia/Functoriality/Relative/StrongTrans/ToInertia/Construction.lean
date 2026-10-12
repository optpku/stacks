/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.ToInertia.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative-to-absolute inertia as a strong transformation

The relative-to-absolute comparison is naturally universe-changing.  Its target first takes
the left endpoint of a pseudo-comma arrow and then applies absolute inertia, so no
universe-stability hypothesis is needed.
-/

@[expose] public section

universe u v u₁ v₁

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
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}

namespace toInertiaStrong

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The universe-changing target of the relative-to-absolute inertia transformation. -/
private def targetPseudofunctor :
    Pseudofunctor
      (Bicategory.PseudoComma
        (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
        (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
      (BasedCategory.{v₁, max u₁ v₁} C) :=
  (Bicategory.PseudoComma.fst
    (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
    (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))).comp
      (BasedCategory.Inertia.pseudofunctor C)

/-- The component of relative-to-absolute inertia at a pseudo-comma arrow. -/
private def component
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))) :
    (pseudofunctor C).obj S ⟶ targetPseudofunctor.obj S :=
  RelativeInertia.toInertia S.hom

/-- Relative-to-absolute inertia is natural in pseudo-comma `2`-morphisms. -/
private theorem naturality_naturality
    {f g : S ⟶ T} (eta : f ⟶ g) :
    (pseudofunctor C).map₂ eta ▷ component T ≫
        (toInertiaIso g).hom =
      (toInertiaIso f).hom ≫
        component S ◁ targetPseudofunctor.map₂ eta := sorry

/-- Identity coherence for the relative-to-absolute inertia comparison. -/
private theorem naturality_id
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))) :
    (toInertiaIso (𝟙 S)).hom ≫
        component S ◁ (targetPseudofunctor.mapId S).hom =
      ((pseudofunctor C).mapId S).hom ▷ component S ≫
        (λ_ (component S)).hom ≫
        (ρ_ (component S)).inv := sorry

/-- Composition coherence for the relative-to-absolute inertia comparison. -/
private theorem naturality_comp
    {R S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : R ⟶ S) (g : S ⟶ T) :
    (toInertiaIso (f ≫ g)).hom ≫
        component R ◁ (targetPseudofunctor.mapComp f g).hom =
      ((pseudofunctor C).mapComp f g).hom ▷ component T ≫
        (α_ _ _ _).hom ≫
        (pseudofunctor C).map f ◁ (toInertiaIso g).hom ≫
        (α_ _ _ _).inv ≫
        (toInertiaIso f).hom ▷ targetPseudofunctor.map g ≫
        (α_ _ _ _).hom := sorry

end toInertiaStrong

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (C) in
/-- Passing from relative inertia to absolute inertia is a universe-changing strong
transformation. Its target takes the left endpoint of a pseudo-comma arrow and then applies
the absolute-inertia pseudofunctor. -/
@[stacks 04Z5 "relative-to-absolute inertia strong transformation"]
def toInertia.strongTrans :
    Pseudofunctor.StrongTrans
      ((pseudofunctor C) :
        Pseudofunctor
          (Bicategory.PseudoComma
            (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
            (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
          (BasedCategory.{v₁, max u₁ v₁} C))
      ((Bicategory.PseudoComma.fst
        (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
        (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))).comp
          (BasedCategory.Inertia.pseudofunctor C)) where
  app S := toInertiaStrong.component S
  naturality f := toInertiaIso f
  naturality_naturality := toInertiaStrong.naturality_naturality
  naturality_id := toInertiaStrong.naturality_id
  naturality_comp := toInertiaStrong.naturality_comp

end pseudoComma
end RelativeInertia

end

end BasedCategory
end CategoryTheory
