module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy.Coproducts
public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv
public import ReasLib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
@stack 08Q4

# Coproducts of simplicial homotopy equivalences

Finite coproducts of simplicial homotopy equivalences are simplicial homotopy equivalences.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.HomotopyEquiv

variable {C : Type u} [Category.{v} C]
variable {T : Type w} [Finite T]
variable {X Y : T → SimplicialObject C}
variable [FunctorCategory.HasPointwiseCoproduct X]
variable [FunctorCategory.HasPointwiseCoproduct Y]

namespace sigmaObj

/-- The coproduct maps of a family of homotopy equivalences satisfy the first
homotopy-inverse law. -/
@[stacks 08Q4 "coproduct homotopy-equivalence first inverse law"]
theorem hom_inv_id (e : ∀ t, HomotopyEquiv (X t) (Y t)) :
    Homotopic
      (Limits.Sigma.map (fun t ↦ (e t).hom) ≫ Limits.Sigma.map (fun t ↦ (e t).inv))
      (𝟙 (∐ X)) := sorry

/-- The coproduct maps of a family of homotopy equivalences satisfy the second
homotopy-inverse law. -/
@[stacks 08Q4 "coproduct homotopy-equivalence second inverse law"]
theorem inv_hom_id (e : ∀ t, HomotopyEquiv (X t) (Y t)) :
    Homotopic
      (Limits.Sigma.map (fun t ↦ (e t).inv) ≫ Limits.Sigma.map (fun t ↦ (e t).hom))
      (𝟙 (∐ Y)) := sorry

end sigmaObj

/-- The finite coproduct of a family of simplicial homotopy equivalences. -/
@[stacks 08Q4 "coproducts of simplicial homotopy equivalences"]
def sigmaObj (e : ∀ t, HomotopyEquiv (X t) (Y t)) :
    HomotopyEquiv (∐ X) (∐ Y) where
  hom := Limits.Sigma.map fun t ↦ (e t).hom
  inv := Limits.Sigma.map fun t ↦ (e t).inv
  hom_inv_id := sigmaObj.hom_inv_id e
  inv_hom_id := sigmaObj.inv_hom_id e

namespace sigmaObj

/-- The forward map of a coproduct homotopy equivalence is the coproduct of the forward maps. -/
@[simp, stacks 08Q4 "forward map of a coproduct homotopy equivalence"]
theorem hom (e : ∀ t, HomotopyEquiv (X t) (Y t)) :
    (sigmaObj e).hom = Limits.Sigma.map (fun t ↦ (e t).hom) := sorry

/-- The inverse map of a coproduct homotopy equivalence is the coproduct of the inverse maps. -/
@[simp, stacks 08Q4 "inverse map of a coproduct homotopy equivalence"]
theorem inv (e : ∀ t, HomotopyEquiv (X t) (Y t)) :
    (sigmaObj e).inv = Limits.Sigma.map (fun t ↦ (e t).inv) := sorry

/-- A finite family of existence-level homotopy equivalences induces an existence-level
homotopy equivalence between the coproducts. -/
@[stacks 08Q4 "coproducts preserve existence of homotopy equivalences"]
theorem nonempty (e : ∀ t, Nonempty (HomotopyEquiv (X t) (Y t))) :
    Nonempty (HomotopyEquiv (∐ X) (∐ Y)) := sorry

end sigmaObj

end CategoryTheory.SimplicialObject.HomotopyEquiv

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The coproduct of a finite family of homotopy-equivalence morphisms is a
homotopy-equivalence morphism. -/
@[stacks 08Q4 "finite coproducts of simplicial homotopy-equivalence morphisms"]
theorem homotopyEquivalences.sigmaMap {T : Type w} [Finite T]
    {X Y : T → SimplicialObject C} [FunctorCategory.HasPointwiseCoproduct X]
    [FunctorCategory.HasPointwiseCoproduct Y] (f : ∀ t, X t ⟶ Y t)
    (hf : ∀ t, homotopyEquivalences C (f t)) :
    homotopyEquivalences C (Limits.Sigma.map f) := sorry

namespace homotopyEquivalences.coproducts

/-- Simplicial homotopy-equivalence morphisms are stable under coproducts of any fixed finite
shape for which the base category has coproducts. -/
@[stacks 08Q4 "finite-shape coproduct stability of simplicial homotopy equivalences"]
theorem ofFiniteShape (J : Type w) [Finite J] [HasCoproductsOfShape J C] :
    (homotopyEquivalences C).IsStableUnderCoproductsOfShape J := sorry

/-- Simplicial homotopy-equivalence morphisms are stable under finite coproducts whenever the
base category has finite coproducts. -/
@[stacks 08Q4 "finite-coproduct stability of simplicial homotopy equivalences"]
instance finite [HasFiniteCoproducts C] :
    (homotopyEquivalences C).IsStableUnderFiniteCoproducts := sorry

end homotopyEquivalences.coproducts

end CategoryTheory.SimplicialObject
