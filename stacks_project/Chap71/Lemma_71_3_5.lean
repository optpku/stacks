/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.FieldExtension
import StacksCheckRecall

/-!
# Lemma 71.3.5

Weak association of a point to a quasi-coherent module on an algebraic space
descends along the projection from a field-extension base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

/- Lemma 71.3.5: Let `K/k` be a field extension. Let `X` be an algebraic space
over `k`. Let `F` be a quasi-coherent `𝒪_X`-module. Let `y` be a point of
`GenericFiber.baseChange k K X` with image `x` in `X`. If `y`
is a weakly associated point of the pullback `FieldExtension.baseChange k K F`, then `x` is a
weakly associated point of `F`. -/
@[stacks 0CUS] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.FieldExtension.mem_weakAss_of_mem_weakAss :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} (F : X.Modules)
    [F.IsQuasicoherent]
    (y : Points (GenericFiber.baseChange k K X))
    (hy : y ∈ (AlgebraicGeometry.AlgebraicSpace.Modules.FieldExtension.baseChange k K F).weakAss),
    Points.map (GenericFiber.toSource k K X) y ∈ F.weakAss)

/- The image of the weakly associated locus of a field-extension pullback is
contained in the weakly associated locus of the original quasi-coherent module. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.FieldExtension.weakAss_map_subset :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} (F : X.Modules)
    [F.IsQuasicoherent],
    Points.map (GenericFiber.toSource k K X) ''
        (AlgebraicGeometry.AlgebraicSpace.Modules.FieldExtension.baseChange k K F).weakAss ⊆
      F.weakAss)
