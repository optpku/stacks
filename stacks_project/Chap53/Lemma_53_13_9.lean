/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ClosedPoint

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 53.13.9: for a smooth proper curve `X` over a field with constant global
functions and genus `g ≥ 2`, there is a closed point whose separable residue field has
degree at most `2 * g - 2`. -/
@[stacks 0CD4] #check
  (AlgebraicGeometry.Curve.exists_closedPoint_finrank_le_two_mul_genus_sub_two :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    [Smooth X.hom]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (g : ℕ)
    (h_genus : g = SchemeOverField.genus X
      (AlgebraicGeometry.topologicalKrullDim_eq_one X) hΓ)
    (h_g : 2 ≤ g),
    ∃ x : X.left, x ∈ closedPoints X.left ∧
      FiniteDimensional k (X.left.residueField x) ∧
      Algebra.IsSeparable k (X.left.residueField x) ∧
      Module.finrank k (X.left.residueField x) ≤ 2 * g - 2)
