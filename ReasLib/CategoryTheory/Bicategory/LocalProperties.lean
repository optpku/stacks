module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.InducedBicategory
public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u

namespace Pseudofunctor

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
variable {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- A pseudofunctor is locally fully faithful when each induced functor on a hom category is
fully faithful. This controls `2`-morphisms while retaining the actual source and target
`1`-morphisms. -/
@[stacks 0040 "locally fully faithful pseudofunctor"]
class IsLocallyFullyFaithful (F : B ⥤ᵖ C) : Prop where
  /-- Every functor induced on a hom category is full. -/
  mapFunctor_full (X Y : B) : (F.mapFunctor X Y).Full
  /-- Every functor induced on a hom category is faithful. -/
  mapFunctor_faithful (X Y : B) : (F.mapFunctor X Y).Faithful

attribute [instance] IsLocallyFullyFaithful.mapFunctor_full
  IsLocallyFullyFaithful.mapFunctor_faithful

/-- A pseudofunctor is locally an equivalence when it induces an equivalence on every hom category.
This name distinguishes equivalence on hom categories from `IsLocallyFullyFaithful`, which only
records fullness and faithfulness on `2`-morphisms. -/
@[stacks 0040 "pseudofunctor inducing equivalences on hom categories"]
class IsLocallyEquivalence (F : B ⥤ᵖ C) : Prop where
  /-- Every functor induced on a hom category is an equivalence. -/
  mapFunctor_isEquivalence (X Y : B) : (F.mapFunctor X Y).IsEquivalence

attribute [instance] IsLocallyEquivalence.mapFunctor_isEquivalence

/-- A pseudofunctor which is locally an equivalence is locally fully faithful. -/
instance IsLocallyEquivalence.toIsLocallyFullyFaithful (F : B ⥤ᵖ C) [F.IsLocallyEquivalence] :
    F.IsLocallyFullyFaithful := sorry
/- Proof strategy: for each hom functor, obtain `Full` and `Faithful` from its
`IsEquivalence` instance. -/

/-- The identity pseudofunctor is locally an equivalence. -/
instance id.isLocallyEquivalence : (Pseudofunctor.id B).IsLocallyEquivalence := sorry
/- Proof strategy: every induced Hom functor is the identity functor, hence an equivalence. -/

universe w₃ v₃ u₃

variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

/-- A composite of locally fully faithful pseudofunctors is locally fully faithful. -/
instance comp.isLocallyFullyFaithful (F : B ⥤ᵖ C) (G : C ⥤ᵖ D)
    [F.IsLocallyFullyFaithful] [G.IsLocallyFullyFaithful] :
    (F.comp G).IsLocallyFullyFaithful := sorry
/- Proof strategy: each induced Hom functor is the composite of the two induced Hom functors;
fullness and faithfulness are closed under composition. -/

/-- A composite of locally equivalent pseudofunctors is locally an equivalence. -/
instance comp.isLocallyEquivalence (F : B ⥤ᵖ C) (G : C ⥤ᵖ D)
    [F.IsLocallyEquivalence] [G.IsLocallyEquivalence] :
    (F.comp G).IsLocallyEquivalence := sorry
/- Proof strategy: each induced Hom functor is the composite of two equivalences of
categories, hence is an equivalence. -/

end Pseudofunctor

end CategoryTheory
