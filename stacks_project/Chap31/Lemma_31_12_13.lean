/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Normal
import StacksCheckRecall

universe u

/- Lemma 31.12.13: let `X` be an integral locally Noetherian normal scheme and let `ℱ` be a
coherent `𝒪_X`-module. The following are equivalent: `ℱ` is reflexive; `ℱ` is torsion-free and
satisfies `(S₂)`; and there is an open subscheme `U` whose complement has irreducible components
of codimension at least two, such that `ℱ|_U` is finite locally free and the canonical map
`ℱ ⟶ j_*j^*ℱ` is an isomorphism. -/
@[stacks 0AY6] #check
  (AlgebraicGeometry.Scheme.Modules.isReflexive_tfae_torsionFree_serreS2_codimTwoOpen :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      [AlgebraicGeometry.IsLocallyNoetherian X]
      (ℱ : X.Modules) [ℱ.IsCoherent],
      X.isNormal →
        List.TFAE
          [ AlgebraicGeometry.Scheme.Modules.IsReflexive ℱ,
            AlgebraicGeometry.Scheme.Modules.IsTorsionFree ℱ ∧
              AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS ℱ 2,
            ∃ U : X.Opens,
              AlgebraicGeometry.Scheme.IdealSheafData.irreducibleComponentsCodimAtLeast
                  2 ((U : Set X)ᶜ : Set X) ∧
                SheafOfModules.IsFiniteLocallyFree
                  ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj ℱ) ∧
                CategoryTheory.IsIso
                  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app ℱ)
          ])
