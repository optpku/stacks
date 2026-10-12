/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive functors on double complexes

Flipping a double complex and taking a coproduct total complex are canonical additive functors.
The instances here let downstream constructions map splittings and homotopies without rebuilding
local additive structures.
-/

@[expose] public section

open CategoryTheory

universe v u w₁ w₂ w₁₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The flip functor preserves addition of morphisms. -/
theorem flip_map_add {I₁ : Type w₁} {I₂ : Type w₂}
    (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
    {K L : HomologicalComplex₂ C c₁ c₂} (f g : K ⟶ L) :
    (flipFunctor C c₁ c₂).map (f + g) =
      (flipFunctor C c₁ c₂).map f + (flipFunctor C c₁ c₂).map g := sorry

/-- Flipping double complexes is an additive functor. -/
@[stacks 0130 "additivity of the double-complex flip functor"]
instance flipFunctorAdditive {I₁ : Type w₁} {I₂ : Type w₂}
    (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) :
    (flipFunctor C c₁ c₂).Additive where
  map_add {_ _} f g := flip_map_add (C := C) c₁ c₂ f g

/-- The map on total complexes preserves addition of bicomplex morphisms. -/
theorem total_map_add {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
    {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    {K L : HomologicalComplex₂ C c₁ c₂} [K.HasTotal c₁₂] [L.HasTotal c₁₂]
    (f g : K ⟶ L) :
    total.map (f + g) c₁₂ = total.map f c₁₂ + total.map g c₁₂ := sorry

/-- Coproduct totalization is an additive functor whenever all of its objectwise totals exist. -/
@[stacks 0130 "additivity of totalization"]
instance totalFunctorAdditive {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
    (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    [∀ K : HomologicalComplex₂ C c₁ c₂, K.HasTotal c₁₂] :
    (totalFunctor C c₁ c₂ c₁₂).Additive where
  map_add {_ _} f g := total_map_add (C := C) (c₁ := c₁) (c₂ := c₂) c₁₂ f g

end HomologicalComplex₂
