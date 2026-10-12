/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy.Products
public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv
public import ReasLib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
@stack 08Q4

# Products of simplicial homotopy equivalences

Finite products of simplicial homotopy equivalences are simplicial homotopy equivalences.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.HomotopyEquiv

variable {C : Type u} [Category.{v} C]
variable {T : Type w} [Finite T]
variable {X Y : T → SimplicialObject C}
variable [FunctorCategory.HasPointwiseProduct X]
variable [FunctorCategory.HasPointwiseProduct Y]

namespace piObj

/-- The product maps of a family of homotopy equivalences satisfy the first homotopy-inverse
law. -/
@[stacks 08Q4 "product homotopy-equivalence first inverse law"]
theorem hom_inv_id (e : ∀ t, HomotopyEquiv (X t) (Y t)) :
    Homotopic
      (Limits.Pi.map (fun t ↦ (e t).hom) ≫ Limits.Pi.map (fun t ↦ (e t).inv))
      (𝟙 (∏ᶜ X)) := sorry

/-- The product maps of a family of homotopy equivalences satisfy the second homotopy-inverse
law. -/
@[stacks 08Q4 "product homotopy-equivalence second inverse law"]
theorem inv_hom_id (e : ∀ t, HomotopyEquiv (X t) (Y t)) :
    Homotopic
      (Limits.Pi.map (fun t ↦ (e t).inv) ≫ Limits.Pi.map (fun t ↦ (e t).hom))
      (𝟙 (∏ᶜ Y)) := sorry

end piObj

/-- The finite product of a family of simplicial homotopy equivalences. -/
@[stacks 08Q4 "products of simplicial homotopy equivalences"]
def piObj (e : ∀ t, HomotopyEquiv (X t) (Y t)) :
    HomotopyEquiv (∏ᶜ X) (∏ᶜ Y) where
  hom := Limits.Pi.map fun t ↦ (e t).hom
  inv := Limits.Pi.map fun t ↦ (e t).inv
  hom_inv_id := piObj.hom_inv_id e
  inv_hom_id := piObj.inv_hom_id e

namespace piObj

/-- The forward map of a product homotopy equivalence is the product of the forward maps. -/
@[simp, stacks 08Q4 "forward map of a product homotopy equivalence"]
theorem hom (e : ∀ t, HomotopyEquiv (X t) (Y t)) :
    (piObj e).hom = Limits.Pi.map (fun t ↦ (e t).hom) := sorry

/-- The inverse map of a product homotopy equivalence is the product of the inverse maps. -/
@[simp, stacks 08Q4 "inverse map of a product homotopy equivalence"]
theorem inv (e : ∀ t, HomotopyEquiv (X t) (Y t)) :
    (piObj e).inv = Limits.Pi.map (fun t ↦ (e t).inv) := sorry

/-- A finite family of existence-level homotopy equivalences induces an existence-level
homotopy equivalence between the products. -/
@[stacks 08Q4 "products preserve existence of homotopy equivalences"]
theorem nonempty (e : ∀ t, Nonempty (HomotopyEquiv (X t) (Y t))) :
    Nonempty (HomotopyEquiv (∏ᶜ X) (∏ᶜ Y)) := sorry

end piObj

end CategoryTheory.SimplicialObject.HomotopyEquiv

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The product of a finite family of homotopy-equivalence morphisms is a homotopy-equivalence
morphism. -/
@[stacks 08Q4 "finite products of simplicial homotopy-equivalence morphisms"]
theorem homotopyEquivalences.piMap {T : Type w} [Finite T]
    {X Y : T → SimplicialObject C} [FunctorCategory.HasPointwiseProduct X]
    [FunctorCategory.HasPointwiseProduct Y] (f : ∀ t, X t ⟶ Y t)
    (hf : ∀ t, homotopyEquivalences C (f t)) :
    homotopyEquivalences C (Limits.Pi.map f) := sorry

namespace homotopyEquivalences.products

/-- Simplicial homotopy-equivalence morphisms are stable under products of any fixed finite
shape for which the base category has products. -/
@[stacks 08Q4 "finite-shape product stability of simplicial homotopy equivalences"]
theorem ofFiniteShape (J : Type w) [Finite J] [HasProductsOfShape J C] :
    (homotopyEquivalences C).IsStableUnderProductsOfShape J := sorry

/-- Simplicial homotopy-equivalence morphisms are stable under finite products whenever the
base category has finite products. -/
@[stacks 08Q4 "finite-product stability of simplicial homotopy equivalences"]
instance finite [HasFiniteProducts C] :
    (homotopyEquivalences C).IsStableUnderFiniteProducts := sorry

end homotopyEquivalences.products

end CategoryTheory.SimplicialObject
