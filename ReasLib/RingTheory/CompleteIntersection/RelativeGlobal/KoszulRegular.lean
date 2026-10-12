/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Local
public import ReasLib.RingTheory.Sequence.Koszul.Regularity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Koszul regularity of relative complete-intersection relations

The displayed relations in a naive polynomial presentation of a relative
global complete intersection form a Koszul-regular finite family.

@stack 07D2
-/

@[expose] public section

universe u

open RingTheory.Sequence

namespace Algebra.Presentation.IsRelativeGlobalCompleteIntersection

variable {R : Type u} [CommRing R]

/-- Lemma 15.33.4, tag `07D2`: the displayed relations
of a naive relative global complete-intersection presentation are Koszul-regular. -/
@[stacks 07D2 "Lemma 15.33.4"]
theorem naive_relations_isKoszulRegularSequence {n c : ℕ}
    {f : Fin c → MvPolynomial (Fin n) R}
    (h : Algebra.Presentation.IsRelativeGlobalCompleteIntersection
      (Algebra.Presentation.naive : Algebra.Presentation R
        (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) (Fin n) (Fin c))) :
    IsKoszulRegularSequence f := sorry

end Algebra.Presentation.IsRelativeGlobalCompleteIntersection
