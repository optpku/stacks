/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.Away.FiniteExtension.PrincipalQuotient
import StacksCheckRecall

@[expose] public section

/-!
# Remark 15.117.4 (0GLU)

The finite principal-quotient lift of Lemma 15.117.3 is functorial for compatible squares of
finite injective extensions and principal-power quotient isomorphisms.

@stack 0GLU
-/

/- Remark 15.117.4: functorial finite lifting of compatible principal-power quotient squares. -/
@[stacks 0GLU "Remark 15.117.4"]
#check @Localization.Away.exists_functorial_finiteExtension_quotientIso

#check @CategoryTheory.CommSq.map_algebraMap_eq
#check @principalPowerIdealQuotientMap
#check @principalIdealQuotientMap
