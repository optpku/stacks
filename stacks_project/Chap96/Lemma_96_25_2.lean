/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Affine.LocallyQuasicoherent
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 96.25.2: For an affine module on a category fibred in groupoids,
étale base-change compatibility, étale sheafhood with quasi-coherent small
affine étale restrictions, and correspondence to a locally quasi-coherent
module under the canonical affine étale comparison are equivalent. -/
@[stacks 0H0F] #check
  (AlgebraicGeometry.GroupoidsOver.locallyQuasicoherentAffine_tfae :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X : AlgebraicGeometry.GroupoidsOver S}
      (F : AlgebraicGeometry.GroupoidsOver.AffineModule X),
      List.TFAE
        [F.EtaleCompatible, F.IsEtaleSheafWithQuasicoherentRestrictions,
          F.CorrespondsToLocallyQuasicoherent])
