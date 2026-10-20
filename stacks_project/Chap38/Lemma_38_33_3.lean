/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Blowup
import StacksCheckRecall

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 38.33.3: a proper morphism of quasi-compact quasi-separated schemes that is an
isomorphism near a closed subset of a quasi-compact open has, after an admissible blowup, a
strict transform that is an isomorphism near the closure of that subset. -/
@[stacks 0F3W] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isAdmissibleBlowup_strictTransform_isIso_near_closure :
    ∀ {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y] [QuasiSeparatedSpace Y]
      (f : X ⟶ Y) [IsProper f]
      (V : Y.Opens) [QuasiCompact V.ι]
      (T : TopologicalSpace.Closeds V)
      (hT : (T : Set V) ⊆ (f ∣_ V).isomorphismLocus),
      ∃ (Y' : Scheme.{u}) (b : Y' ⟶ Y) (I : Y.IdealSheafData),
        IsAdmissibleBlowupCenter V b I ∧
          closure (b.base ⁻¹' Set.image V.ι.base (T : Set V)) ⊆
            (strictTransformSnd b (I.comap b) f).isomorphismLocus)

end AlgebraicGeometry
