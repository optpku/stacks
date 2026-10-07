module

public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Additivity of Left Exact Functors

Finite-limit-preserving functors between preadditive categories with the
relevant finite limits are additive.
-/

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]

/-- A finite-limit-preserving functor between preadditive categories with zero
objects and binary products preserves addition. -/
@[stacks 015S]
instance (priority := 90) additive_of_preservesFiniteLimits
    [HasZeroObject C] [HasBinaryProducts C] [HasZeroObject D]
    (F : C ⥤ D) [PreservesFiniteLimits F] : F.Additive := sorry

/-- The underlying functor of a bundled left-exact functor is additive. -/
@[stacks 015S]
instance additive_of_leftExact (F : C ⥤ₗ D) [HasZeroObject C] [HasBinaryProducts C]
    [HasZeroObject D] : F.obj.Additive :=
  additive_of_preservesFiniteLimits F.obj

end CategoryTheory.Functor
