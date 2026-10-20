/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Reduced
import StacksCheckRecall

/-!
# Lemma 28.20.3 compatibility entry point

The reduced-scheme refinement of the finite-local-freeness criterion is owned by
`ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Reduced`.
-/

universe u

/- Lemma 28.20.3: for a quasi-coherent module on a reduced scheme, the five standard
finite-local-freeness conditions are also equivalent to finite type with locally constant fiber
rank. -/
@[stacks 0FWH] #check
  (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_tfae_of_isReduced :
    {X : AlgebraicGeometry.Scheme.{u}} → (ℱ : X.Modules) → [ℱ.IsQuasicoherent] →
      [AlgebraicGeometry.IsReduced X] →
      List.TFAE [
        AlgebraicGeometry.Scheme.Modules.FinitePresentationFlat ℱ,
        AlgebraicGeometry.Scheme.Modules.FinitePresentationStalkwiseFree ℱ,
        AlgebraicGeometry.Scheme.Modules.LocallyFreeFiniteType ℱ,
        SheafOfModules.IsFiniteLocallyFree ℱ,
        AlgebraicGeometry.Scheme.Modules.FiniteTypeStalkwiseFreeRankLocallyConstant ℱ,
        AlgebraicGeometry.Scheme.Modules.FiniteTypeRankLocallyConstant ℱ])
