/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.Pseudofunctor.Mapping
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Action.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Comparison.Identity.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Comparison.Composition.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Pseudofunctor.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for pseudo-comma relative inertia

This leaf identifies the object, square, `2`-cell, local hom, identity
comparison, and composition comparison fields of the relative-inertia
pseudofunctor with their reusable lower-level owners.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace RelativeInertia
namespace pseudoComma

noncomputable section

/-- The object action of the relative-inertia pseudofunctor is the relative inertia of the
structural pseudo-comma arrow. -/
@[simp, stacks 04Z4 "relative-inertia pseudofunctor object computation"]
theorem pseudofunctor.obj
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))) :
    (pseudofunctor C).obj S = relativeInertia S.hom := sorry

/-- The `1`-cell action of the relative-inertia pseudofunctor is the map induced by the
corresponding invertibly commuting square. -/
@[simp, stacks 04Z4 "relative-inertia pseudofunctor map computation"]
theorem pseudofunctor.map
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) :
    (pseudofunctor C).map f = pseudoComma.map f := sorry

/-- The `2`-cell action of the relative-inertia pseudofunctor is the induced based natural
transformation between square maps. -/
@[simp, stacks 04Z4 "relative-inertia pseudofunctor 2-cell computation"]
theorem pseudofunctor.map₂
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    {f g : S ⟶ T} (η : f ⟶ g) :
    (pseudofunctor C).map₂ η = pseudoComma.map₂ η := sorry

/-- On each hom category, the relative-inertia pseudofunctor is the explicit pseudo-comma
relative-inertia hom functor. -/
@[simp, stacks 04Z4 "relative-inertia pseudofunctor hom-functor computation"]
theorem pseudofunctor.mapFunctor
    (S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))) :
    (pseudofunctor C).mapFunctor S T = pseudoComma.mapFunctor S T := sorry

/-- The identity comparison of the relative-inertia pseudofunctor is the explicit objectwise
identity isomorphism. -/
@[simp, stacks 04Z4 "relative-inertia pseudofunctor identity comparison computation"]
theorem pseudofunctor.mapId
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))) :
    (pseudofunctor C).mapId S = mapIdIso S := sorry

/-- The composition comparison of the relative-inertia pseudofunctor is the explicit
objectwise composition isomorphism. -/
@[simp, stacks 04Z4 "relative-inertia pseudofunctor composition comparison computation"]
theorem pseudofunctor.mapComp
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) (g : T ⟶ U) :
    (pseudofunctor C).mapComp f g = mapCompIso f g := sorry

end

end pseudoComma
end RelativeInertia
end BasedCategory
end CategoryTheory
