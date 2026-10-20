module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Subobject.FactorThru
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Factorizations Through Injective Subobjects

This module packages the concrete data of a morphism factoring through an injective subobject of
its target.  It is independent of cochain complexes and can be reused whenever an injective piece
inside a fixed ambient object is needed.
-/

open CategoryTheory

universe v u

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C] {X Y : C}

/-- A concrete factorization of `f : X ⟶ Y` through an injective subobject of `Y`.

Unlike the proposition `Subobject.Factors`, this structure retains both the chosen subobject and
the actual factor map as reusable data. -/
@[stacks 079N "injective subobject factorization"]
structure InjectiveFactor (f : X ⟶ Y) where
  /-- The chosen injective subobject of the target. -/
  subobject : Subobject Y
  /-- The underlying object of the chosen subobject is injective. -/
  injective : Injective (subobject : C)
  /-- The map from the source to the chosen subobject. -/
  lift : X ⟶ subobject
  /-- The factor map followed by the subobject inclusion is the original morphism. -/
  lift_arrow : lift ≫ subobject.arrow = f

attribute [instance] InjectiveFactor.injective

namespace InjectiveFactor

/-- The chosen subobject of an injective-subobject factorization contains the original map. -/
theorem factors {f : X ⟶ Y} (F : InjectiveFactor f) : F.subobject.Factors f := sorry

/-- Injective-subobject factorizations are equivalent at the proposition level to the usual
existence statement phrased with `Subobject.Factors`. -/
theorem nonempty_iff (f : X ⟶ Y) :
    Nonempty (InjectiveFactor f) ↔
      ∃ I : Subobject Y, Injective (I : C) ∧ I.Factors f := sorry

end InjectiveFactor

end CategoryTheory.Subobject
