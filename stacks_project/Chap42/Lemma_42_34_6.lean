/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowCohomology.FirstChern.Vanishing

open AlgebraicGeometry CategoryTheory
open scoped DirectSum

universe u

/- Lemma 42.34.6: On a finite-type scheme of dimension `d` over a universally
catenary dimensioned base, admitting an ample invertible module, the ordered product
of any `d + 1` first Chern classes vanishes in the Chow cohomology ring. -/
@[stacks 0FDX] #check (AlgebraicGeometry.ChowCohomology.prod_firstChernClass_eq_zero :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [Scheme.Hom.FiniteType p] {d : ℕ}
    (hXdim : topologicalKrullDim X = d)
    (hample : Scheme.Modules.HasAmpleInvertibleModule X)
    (L : Fin (d + 1) → X.Modules)
    [∀ i : Fin (d + 1), Scheme.Modules.Invertible (L i)],
    (List.ofFn fun i : Fin (d + 1) ↦
      DirectSum.of (AlgebraicGeometry.ChowCohomology.degree δ p) (1 : ℤ)
        (AlgebraicGeometry.ChowCohomology.firstChernClass δ p (L i))).prod =
      (0 : AlgebraicGeometry.ChowCohomology.ring δ p))
