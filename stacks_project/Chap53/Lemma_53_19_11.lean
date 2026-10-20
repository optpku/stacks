/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.SplitNode.Criteria

@[expose] public section

open AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Hom.PointsOver
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.19.11: for a one-dimensional algebraic scheme over a field and a closed point,
the split-node condition, the exhaustive two-point normalization condition with residue-field
identifications, and the completed-local-ring presentation by `k[[u, v]]/(uv)` are equivalent.
The supplied source ends with the literal placeholder `add more here`; this statement records
the three assertions that are mathematically specified. -/
@[stacks 0CBW] #check
  (AlgebraicGeometry.SchemeOverField.isSplitNode_tfae :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X]
    (h_dimension : topologicalKrullDim X.left = 1)
    (x : X.left) (h_closed : x ∈ closedPoints X.left),
    List.TFAE
      [ isSplitNode X h_dimension x
      , isNode X x ∧
          Function.Bijective (algebraMap k (ResidueField (stalkRing X x))) ∧
          ∃ x₁ x₂ : pointsOver X.left.normalizationTo x,
            x₁ ≠ x₂ ∧
              (∀ y : pointsOver X.left.normalizationTo x, y = x₁ ∨ y = x₂) ∧
                Function.Bijective
                  (residueFieldMap X.left.normalizationTo x x₁).hom ∧
                  Function.Bijective
                    (residueFieldMap X.left.normalizationTo x x₂).hom
      , Nonempty
          (AdicCompletion (maximalIdeal (stalkRing X x)) (stalkRing X x) ≃ₐ[k]
            (MvPowerSeries (Fin 2) k ⧸
              Ideal.span
                {((MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)) :
                  MvPowerSeries (Fin 2) k)}))
      ])

end AlgebraicGeometry.SchemeOverField
