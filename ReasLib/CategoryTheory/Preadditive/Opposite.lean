module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.CategoryTheory.Preadditive.Transfer
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive structures and opposite categories

The forward opposite constructions are coherent instances.  Constructions recovering structure
on `C` from structure on `Cᵒᵖ` are explicit definitions, since registering both directions would
create typeclass-search cycles.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Preadditive

open CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/-- Recover the preadditive structure on `C` explicitly from one on `Cᵒᵖ`.  This is deliberately
not an instance, to avoid a cycle with `instPreadditiveOpposite`. -/
@[stacks 010A, implicit_reducible]
noncomputable def ofOpposite [Preadditive Cᵒᵖ] : Preadditive C :=
  @Preadditive.ofFullyFaithful C _ Cᵒᵖᵒᵖ _
    (CategoryTheory.instPreadditiveOpposite Cᵒᵖ) (opOp C)
    (Functor.FullyFaithful.ofFullyFaithful (opOp C))

/-- Finite products in a preadditive category give a canonical finite-coproduct structure through
finite biproducts.  The result is explicit because concrete categories may prefer another model. -/
theorem hasFiniteCoproductsOfFiniteProducts
    [Preadditive C] [HasFiniteProducts C] : HasFiniteCoproducts C := sorry

/-- A preadditive category with finite products has finite products on its opposite category. -/
noncomputable instance hasFiniteProducts_opposite
    [Preadditive C] [HasFiniteProducts C] : HasFiniteProducts Cᵒᵖ :=
  @CategoryTheory.Limits.hasFiniteProducts_opposite C _
    (hasFiniteCoproductsOfFiniteProducts C)

/-- Recover finite products on `C` explicitly from a preadditive finite-product structure on
`Cᵒᵖ`.  This is not registered as an instance, to avoid opposite-direction search loops. -/
theorem hasFiniteProductsOfOpposite
    [Preadditive Cᵒᵖ] [HasFiniteProducts Cᵒᵖ] : HasFiniteProducts C := sorry

end CategoryTheory.Preadditive
