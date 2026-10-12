/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.OpenImmersion
import StacksCheckRecall

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 38.31.3: a separated finite-type morphism that is an isomorphism over a
quasi-compact open has an open strict transform after a suitable admissible blowup. -/
@[stacks 081S] #check
  (AlgebraicGeometry.exists_isAdmissibleBlowup_strictTransform_isOpenImmersion :
    ∀ {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
      (f : X ⟶ S) [IsSeparated f] [Scheme.Hom.FiniteType f]
      (U : S.Opens) [QuasiCompact U.ι] [IsIso (f ∣_ U)],
      ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (I : S.IdealSheafData),
      IsAdmissibleBlowupCenter U b I ∧
        IsOpenImmersion (strictTransformSnd b (I.comap b) f))

end AlgebraicGeometry
