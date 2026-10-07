module

public import Mathlib.AlgebraicTopology.DoldKan.FunctorGamma
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additivity of the Dold--Kan `Γ₀` functor

This file records the algebraic property of `Γ₀` needed by reusable short-complex constructions.
The induced `PreservesZeroMorphisms` instance is supplied by the standard additive-functor API.

@stack 0192
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicTopology.DoldKan.Γ₀

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

/-- The Dold--Kan `Γ₀` functor is additive in every preadditive category with finite
coproducts. -/
@[stacks 0192 "additivity of the Dold-Kan Γ₀ functor"]
instance additive :
    (AlgebraicTopology.DoldKan.Γ₀ :
      ChainComplex C ℕ ⥤ SimplicialObject C).Additive := sorry

end AlgebraicTopology.DoldKan.Γ₀
