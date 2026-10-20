/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Blowup
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 38.31.2: a proper morphism over a quasi-compact quasi-separated scheme that is finite
locally free over a quasi-compact open admits an admissible blowup whose strict transform is
finite locally free. -/
@[stacks 0B49] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isAdmissibleBlowup_finiteLocallyFree :
    ∀ {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
      (f : X ⟶ S) [IsProper f]
      (U : S.Opens) [QuasiCompact U.ι]
      [IsFiniteLocallyFree (f ∣_ U)],
      ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (I : S.IdealSheafData),
        IsAdmissibleBlowupCenter U b I ∧
          IsFiniteLocallyFree (strictTransformSnd b (I.comap b) f))

end AlgebraicGeometry
