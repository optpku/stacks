module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Sites.EnoughObjects
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Modules on sites with enough weakly contractible objects

This leaf owns the ordinary-category consequences of testing module sheaves on weakly
contractible objects.  Derived truncation and Milnor consequences live in the corresponding
`Module.Derived.Limit` leaf.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe z u v w

namespace RingedSite.ModuleCat.WeaklyContractible

variable (X : RingedSite.{u, v, w})
variable [UnivLE.{max u v, z}]

/-- Exactness of a short complex of module sheaves can be tested on a covering family of weakly
contractible objects. -/
@[stacks 0947 "exactness on weakly contractible objects"]
theorem exact_iff_evaluation
    (B : Set X)
    (hweak : ∀ ⦃U : X⦄, U ∈ B → X.siteTopology.IsWeaklyContractible U)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (S : ShortComplex (RingedSite.ModuleCat.{z} X)) :
    S.Exact ↔
      ∀ ⦃U : X⦄, U ∈ B →
        (S.map (SheafOfModules.evaluation.{z} X.structureSheaf (op U))).Exact := sorry

/-- For a tower with epimorphic transitions, the projection of its limit to the zeroth stage is
epimorphic when the site has enough weakly contractible objects. -/
@[stacks 0947 "surjective inverse-limit projection"]
theorem limit_π_zero_epi
    (hEnough : X.siteTopology.HasEnoughObjectsWithProperty
      X.siteTopology.IsWeaklyContractible)
    (F : SequentialInverseSystem (RingedSite.ModuleCat.{z} X))
    (h_epi : ∀ n : ℕ, Epi (F.stepMap n)) :
    Epi (limit.π F (op 0)) := sorry

/-- Products of module sheaves are exact when the site has enough weakly contractible objects. -/
@[stacks 0947 "exact products from weakly contractible objects"]
theorem ab4Star
    [HasProducts (RingedSite.ModuleCat.{z} X)]
    (hEnough : X.siteTopology.HasEnoughObjectsWithProperty
      X.siteTopology.IsWeaklyContractible) :
    AB4Star (RingedSite.ModuleCat.{z} X) := sorry

/-- A fact recording enough weakly contractible objects exposes exact products to typeclass
search. -/
@[stacks 0947 "exact-products instance from weakly contractible objects"]
noncomputable instance instAB4Star
    [HasProducts (RingedSite.ModuleCat.{z} X)]
    [Fact (X.siteTopology.HasEnoughObjectsWithProperty
      X.siteTopology.IsWeaklyContractible)] :
    AB4Star (RingedSite.ModuleCat.{z} X) := sorry

/-- A fact for enough weakly contractible objects exposes exact countable products to the generic
derived-limit API. -/
@[stacks 0947 "countable exact products from weakly contractible objects"]
noncomputable instance instCountableAB4Star
    [HasCountableProducts (RingedSite.ModuleCat.{z} X)]
    [Fact (X.siteTopology.HasEnoughObjectsWithProperty
      X.siteTopology.IsWeaklyContractible)] :
    CountableAB4Star (RingedSite.ModuleCat.{z} X) := sorry

end RingedSite.ModuleCat.WeaklyContractible

end
