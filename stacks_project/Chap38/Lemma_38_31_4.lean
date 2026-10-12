/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Domination
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 38.31.4: a proper morphism that is an isomorphism over a quasi-compact open of a
quasi-compact quasi-separated base is dominated by an admissible blowup away from that open. -/
@[stacks 081T] #check (AlgebraicGeometry.exists_isAdmissibleBlowup_dominating :
    ∀ {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
      (f : X ⟶ S) [IsProper f]
      (U : S.Opens) [QuasiCompact U.ι] [IsIso (f ∣_ U)],
      ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (g : S' ⟶ X),
        IsAdmissibleBlowup U b ∧ g ≫ f = b)

end AlgebraicGeometry
