/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.Cotangent.KaehlerFiber
public import ReasLib.RingTheory.Smooth.AtPrime.Regularity
import StacksCheckRecall

/-!
@stack 00TS

The four source clauses are recalled through pairwise `SmoothAtPrime` criteria.  The residue-field
comparison below identifies their canonical Kähler fiber with the quotient-field spelling in the
source.
-/

@[expose] public section

/- Lemma 10.140.2 (4): smoothness at a prime is smoothness on a principal-open neighborhood. -/
@[stacks 00TS "(4), principal-open neighborhood"]
#check @Algebra.SmoothAtPrime.iff_exists_away

/- Lemma 10.140.2, `(1) ↔ (4)`: smoothness at a closed point is equivalent to regularity of its
local ring. -/
@[stacks 00TS "(1) iff (4), regular local ring"]
#check @Algebra.SmoothAtPrime.iff_isRegularLocalRing_at_maximal

/- Lemma 10.140.2, `(2) ↔ (4)`: smoothness is equivalent to the Kähler-fiber dimension bound. -/
@[stacks 00TS "(2) iff (4), fiber-dimension bound"]
#check @Algebra.SmoothAtPrime.iff_fiberFinrank_le_localDimension_at_maximal

/- Lemma 10.140.2, `(3) ↔ (4)`: smoothness is equivalent to equality in the Kähler-fiber
dimension bound. -/
@[stacks 00TS "(3) iff (4), fiber-dimension equality"]
#check @Algebra.SmoothAtPrime.iff_fiberFinrank_eq_localDimension_at_maximal

/- The source writes the residue field of a maximal ideal as its quotient field. -/
@[stacks 00TS "quotient-field fiber view"]
#check @Ideal.ResidueField.finrank_tensor_eq_quotient
