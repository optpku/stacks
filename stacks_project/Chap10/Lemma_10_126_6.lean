/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.AtPrime.LocalProduct
import StacksCheckRecall

@[expose] public section

/-!
# Principal-open product splitting

@stack 00QR

The reusable statement is owned by `Algebra.FinitePresentation`: finite presentation and a
bijective map on the chosen local rings yield a product decomposition after restricting to one
principal open neighbourhood.
-/

/- Lemma 10.126.6 (Tag 00QR). -/
@[stacks 00QR]
#check @Algebra.FinitePresentation.exists_away_product_of_localRingHom_bijective

end
