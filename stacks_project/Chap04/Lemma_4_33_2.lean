/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {S : Type u₁} [Category.{v₁} S]
variable {E : Type u₂} [Category.{v₂} E]
variable (p : E ⥤ S)
variable {R T U : S} {x y z : E}
variable {f : R ⟶ T} {g : T ⟶ U} {phi : x ⟶ y} {psi : y ⟶ z}

/- The source's three closure properties are exactly the installed
`CategoryTheory.Functor.IsStronglyCartesian` instances/theorem `comp`, `of_isIso`, and
`isIso_of_base_isIso`. The weaker `IsCartesian` API and dual `IsStronglyCocartesian` API do not
match the source. Recalling the canonical owner introduces only universe polymorphism; specializing
the explicit base arrows to the images under `p` recovers the arrow-only textbook wording and
leaves the instances directly reusable by typeclass search. -/

/- Lemma 4.33.2 (1): the composite of strongly cartesian morphisms is the canonical instance
`comp`. -/
@[stacks 02XL "composition of strongly cartesian morphisms"]
#check @Functor.IsStronglyCartesian.comp

/- Lemma 4.33.2 (2): an isomorphism is strongly cartesian over its image in the base category by
the canonical instance `of_isIso`. -/
@[stacks 02XL "isomorphisms are strongly cartesian"]
#check (fun [p.IsHomLift f phi] [IsIso phi] =>
  Functor.IsStronglyCartesian.of_isIso p f phi :
  forall [p.IsHomLift f phi] [IsIso phi], p.IsStronglyCartesian f phi)

/- Lemma 4.33.2 (3): a strongly cartesian morphism whose image in the base category is an
isomorphism is itself an isomorphism by the canonical theorem
`isIso_of_base_isIso`. -/
@[stacks 02XL "a strongly cartesian morphism over an isomorphism is an isomorphism"]
#check (fun [p.IsStronglyCartesian f phi] [IsIso f] =>
  Functor.IsStronglyCartesian.isIso_of_base_isIso p f phi :
  forall [p.IsStronglyCartesian f phi] [IsIso f], IsIso phi)

end CategoryTheory
