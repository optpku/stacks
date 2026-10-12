/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Idempotents
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 110.45.1 -/
@[stacks 04QL]
#check (AlgebraicGeometry.exists_affine_closedSubscheme_locally_cutOutByIdempotents_not_globally :
    ∃ (A : CommRingCat.{u}) (T : (Spec A).IdealSheafData),
      T.IsLocallyCutOutByIdempotents ∧ ¬ T.IsCutOutByIdempotents)
