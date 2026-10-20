/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalRing.Nodal

@[expose] public section

open IsLocalRing

universe u v

/- Lemma 53.19.3 -/
@[stacks 0C49] #check
  (IsLocalRing.nodalLocalAlgebra_tfae :
    ∀ (k : Type u) [Field k]
      (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A],
    let κ := ResidueField A
    let V := CotangentSpace A
    let hasQuadraticRelation :=
      ∃ (e : Module.Basis (Fin 2) κ V) (a b c : κ),
        4 * a * c - b ^ 2 ≠ 0 ∧
          idealConormalAlgebraQuotient (maximalIdeal A)
              (a • SymmetricAlgebra.ι κ V (e 0) ^ 2 +
                b • (SymmetricAlgebra.ι κ V (e 0) * SymmetricAlgebra.ι κ V (e 1)) +
                c • SymmetricAlgebra.ι κ V (e 1) ^ 2) = 0
    let reducedCondition :=
      Algebra.IsSeparableOver k κ ∧ IsReduced A ∧
        Module.finrank κ V = 2 ∧ hasQuadraticRelation
    let depthCondition :=
      Algebra.IsSeparableOver k κ ∧ moduleDepth A A = 1 ∧
        Module.finrank κ V = 2 ∧ hasQuadraticRelation
    let completionCondition :=
      Algebra.IsSeparableOver k κ ∧
        ∃ a b c : κ, 4 * a * c - b ^ 2 ≠ 0 ∧
          Nonempty
            ((MvPowerSeries (Fin 2) κ ⧸
                Ideal.span
                  {algebraMap κ (MvPowerSeries (Fin 2) κ) a *
                      MvPowerSeries.X (0 : Fin 2) ^ 2 +
                    algebraMap κ (MvPowerSeries (Fin 2) κ) b *
                      (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)) +
                    algebraMap κ (MvPowerSeries (Fin 2) κ) c *
                      MvPowerSeries.X (1 : Fin 2) ^ 2}) ≃ₐ[k]
              AdicCompletion (maximalIdeal A) A)
    List.TFAE [reducedCondition, depthCondition, completionCondition])
