/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal.Blowup
import StacksCheckRecall

/-!
# Lemma 71.18.10

If a finite-type quasi-coherent module on an algebraic space is locally free of
rank `k` off the closed subspace cut out by `Fit_k(F)`, then its strict
transform under the blowup in that subspace is locally free of rank `k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.18.10: A finite-type quasi-coherent module locally free of rank `k`
outside its `k`th Fitting center has strict transform locally free of rank `k`
under the blowup in that center. -/
@[stacks 0D0Q] #check
  (AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf.strictTransformModule_isFiniteLocallyFreeOfRank :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (F : B.Modules)
      [F.IsFiniteType] [F.IsQuasicoherent] (k : ℕ)
      (π : Blowup B (fittingIdealSheaf F k))
      [SheafOfModules.IsFiniteLocallyFreeOfRank k
      ((Modules.pullback (closedImmersionComplementι
          (subschemeι (fittingIdealSheaf F k)))).obj F)],
    SheafOfModules.IsFiniteLocallyFreeOfRank k
      (strictTransformModule π.hom (Blowup.exceptionalDivisor π) (𝟙 B) F))
