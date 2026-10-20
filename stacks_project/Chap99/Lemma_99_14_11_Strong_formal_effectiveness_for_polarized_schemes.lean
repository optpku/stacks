/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Polarized.FormalSystem.Algebraization

/-!
# Strong formal effectiveness for polarized schemes

Algebraization of a cartesian tower of proper flat finite-presentation schemes
with compatible invertible modules, ample at the first stage, over the spectrum
of a sequential inverse limit of rings.

Lean stage `0` corresponds to source stage `1`; initial-stage ampleness is
the source hypothesis that `L_1` is ample on `X_1`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 99.14.11 (Strong formal effectiveness for polarized schemes): A compatible polarized formal system admits algebraization. -/
@[stacks 0D4T] #check
  (AlgebraicGeometry.Polarized.strongFormalEffectiveness :
    ∀ (ξ : AlgebraicGeometry.Polarized.FormalSystem.{u}),
      ∃ (X : Scheme.{u}) (f : X ⟶ ξ.limitSpec) (L : X.Modules)
        (hf_proper : IsProper f) (hf_flat : Flat f)
        (hf_fp : Scheme.Hom.FinitePresentation f)
        (hL_inv : Scheme.Modules.Invertible L)
        (hL_ample : @Scheme.Modules.IsAmple X L hL_inv)
        (cX : ∀ n, ξ.X n ⟶ X)
        (hcX_pullback :
          ∀ n, IsPullback (cX n) (ξ.hom n) f (ξ.stageToLimit n))
        (cL : ∀ n, (Scheme.Modules.pullback (cX n)).obj L ≅ ξ.line n)
        (hcX_comp : ∀ n, cX n = ξ.step n ≫ cX (n + 1)),
        ∀ n,
          cL n =
            (Scheme.Modules.pullbackCongr (hcX_comp n)).app L ≪≫
              (Scheme.Modules.pullbackComp (ξ.step n) (cX (n + 1))).symm.app L ≪≫
                (Scheme.Modules.pullback (ξ.step n)).mapIso (cL (n + 1)) ≪≫
                  ξ.iso n)
