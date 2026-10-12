/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Blowup
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 38.31.1: a finite-type quasi-separated morphism that is flat and locally of finite
presentation over a quasi-compact open has a flat finitely presented strict transform after an
admissible blowup away from that open. -/
@[stacks 081R] #check
  (AlgebraicGeometry.Scheme.Hom.exists_isAdmissibleBlowup_flattening :
    ∀ {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
      (f : X ⟶ S) [Scheme.Hom.FiniteType f] [QuasiSeparated f]
      (U : S.Opens) [QuasiCompact U.ι]
      [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)],
      ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (I : S.IdealSheafData),
        IsAdmissibleBlowupCenter U b I ∧
          let f' := strictTransformSnd b (I.comap b) f
          Flat f' ∧ Scheme.Hom.FinitePresentation f')

end AlgebraicGeometry
