module

public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Noetherian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-Length Objects in Abelian Categories

This file packages the Artinian and Noetherian conditions as the object property
`isFiniteLengthObject`.  It also supplies the missing Serre-class instances and the corresponding
short-exact-sequence API.
-/

@[expose] public section

open Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Noetherianity of an object in an abelian category is Artinianity of its opposite. -/
theorem isNoetherianObject_iff_isArtinianObject_op [Abelian C] (X : C) :
    IsNoetherianObject X ↔ IsArtinianObject (op X) := sorry

/-- Artinianity of an object in an abelian category is Noetherianity of its opposite. -/
theorem isArtinianObject_iff_isNoetherianObject_op [Abelian C] (X : C) :
    IsArtinianObject X ↔ IsNoetherianObject (op X) := sorry

/-- The object property of being both Artinian and Noetherian. -/
def isFiniteLengthObject : ObjectProperty C :=
  isArtinianObject ⊓ isNoetherianObject

/-- An object has finite length when it is both Artinian and Noetherian. -/
abbrev IsFiniteLengthObject (X : C) : Prop :=
  isFiniteLengthObject.Is X

/-- A finite-length object is Artinian. -/
instance instIsArtinianObjectOfIsFiniteLengthObject (X : C) [IsFiniteLengthObject X] :
    IsArtinianObject X := sorry

/-- A finite-length object is Noetherian. -/
instance instIsNoetherianObjectOfIsFiniteLengthObject (X : C) [IsFiniteLengthObject X] :
    IsNoetherianObject X := sorry

/-- The finite-length object property unfolds to the conjunction of the Artinian and Noetherian
conditions. -/
theorem isFiniteLengthObject_iff (X : C) :
    IsFiniteLengthObject X ↔ IsArtinianObject X ∧ IsNoetherianObject X := sorry

/-- Artinian objects form a Serre class in an abelian category. -/
instance isArtinianObject_isSerreClass [Abelian C] :
    (isArtinianObject : ObjectProperty C).IsSerreClass := sorry

/-- Noetherian objects form a Serre class in an abelian category. -/
instance isNoetherianObject_isSerreClass [Abelian C] :
    (isNoetherianObject : ObjectProperty C).IsSerreClass := sorry

/-- Finite-length objects form a Serre class in an abelian category. -/
instance isFiniteLengthObject_isSerreClass [Abelian C] :
    (isFiniteLengthObject : ObjectProperty C).IsSerreClass := sorry

namespace ShortComplex

variable [Abelian C] {S : ShortComplex C}

/-- Lemma 12.9.4 (Tag 0FCH): in a short exact sequence, the middle object is Artinian exactly
when the two outer objects are Artinian. -/
@[stacks 0FCH]
theorem isArtinianObject_iff_of_shortExact (hS : S.ShortExact) :
    IsArtinianObject S.X₂ ↔ IsArtinianObject S.X₁ ∧ IsArtinianObject S.X₃ := sorry

/-- Lemma 12.9.5 (Tag 0FCI): in a short exact sequence, the middle object is Noetherian exactly
when the two outer objects are Noetherian. -/
@[stacks 0FCI]
theorem isNoetherianObject_iff_of_shortExact (hS : S.ShortExact) :
    IsNoetherianObject S.X₂ ↔ IsNoetherianObject S.X₁ ∧ IsNoetherianObject S.X₃ := sorry

/-- In a short exact sequence, the middle object has finite length exactly when the two outer
objects have finite length. -/
theorem isFiniteLengthObject_iff_of_shortExact (hS : S.ShortExact) :
    IsFiniteLengthObject S.X₂ ↔ IsFiniteLengthObject S.X₁ ∧ IsFiniteLengthObject S.X₃ := sorry

end ShortComplex

end CategoryTheory
