/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtration.Map
public import ReasLib.CategoryTheory.Filtration.Preadditive

/-!
# Additive Functoriality of Filtered Objects

This leaf supplies additive instances for the functors constructed in
`Filtration.Map`.  The mono-preserving filtration construction itself remains available without
preadditive assumptions.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

namespace FilteredObject

section Additive

/-- Stacks 015S: the filtered-object functor induced by an additive mono-preserving functor is
additive. -/
@[stacks 015S]
instance mapFunctor_additive (F : C ⥤ D) [F.PreservesMonomorphisms]
    [Preadditive C] [Preadditive D] [F.Additive] :
    (mapFunctor F).Additive := sorry

/-- Stacks 015S: the induced functor between finite-filtered-object categories is additive. -/
@[stacks 015S]
instance Finite.mapFunctor_additive (F : C ⥤ D) [F.PreservesMonomorphisms]
    [Preadditive C] [Preadditive D] [F.Additive]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    [HasZeroObject C] [HasZeroObject D] [F.PreservesZeroMorphisms] :
    (Finite.mapFunctor F).Additive := sorry

end Additive

end FilteredObject
end CategoryTheory
