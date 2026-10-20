module

public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.ChowCohomology.FirstChern.Commutation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

open CategoryTheory
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChowCohomology

/-- On a finite-type scheme of dimension `d` over a universally catenary dimensioned base
admitting an ample invertible module, the product of any `d + 1` first Chern classes vanishes. -/
theorem prod_firstChernClass_eq_zero
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [Scheme.Hom.FiniteType p] {d : ℕ}
    (hXdim : topologicalKrullDim X = d)
    (hample : Scheme.Modules.HasAmpleInvertibleModule X)
    (L : Fin (d + 1) → X.Modules)
    [∀ i : Fin (d + 1), Scheme.Modules.Invertible (L i)] :
    (List.ofFn fun i : Fin (d + 1) ↦
      DirectSum.of (degree δ p) (1 : ℤ) (firstChernClass δ p (L i))).prod =
        (0 : ring δ p) := sorry

end AlgebraicGeometry.ChowCohomology
