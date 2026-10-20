/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.TFAE
import StacksCheckRecall

/-!
# Lemma 28.20.2 compatibility entry point

The quasi-coherent finite-local-freeness criterion is owned by
`ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.TFAE`.
-/

universe u

/- Lemma 28.20.2: for a quasi-coherent module on a scheme, finite-presentation flatness,
finite presentation with free stalks, local freeness of finite type, finite local freeness, and
finite type with free stalks and locally constant fiber rank are equivalent. -/
@[stacks 05P2] #check (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_tfae :
  {X : AlgebraicGeometry.Scheme.{u}} → (ℱ : X.Modules) → [ℱ.IsQuasicoherent] →
    List.TFAE [
      AlgebraicGeometry.Scheme.Modules.FinitePresentationFlat ℱ,
      AlgebraicGeometry.Scheme.Modules.FinitePresentationStalkwiseFree ℱ,
      AlgebraicGeometry.Scheme.Modules.LocallyFreeFiniteType ℱ,
      SheafOfModules.IsFiniteLocallyFree ℱ,
      AlgebraicGeometry.Scheme.Modules.FiniteTypeStalkwiseFreeRankLocallyConstant ℱ])
