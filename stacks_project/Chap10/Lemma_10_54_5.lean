/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.EssentialFiniteness.LocalPresentation
import StacksCheckRecall

@[expose] public section

/-!
# A local polynomial presentation for an essentially finite type map

@stack 0AUG
-/

/- Lemma 10.54.5: an essentially finite type map between local rings is a
localization of a quotient of a suitable local polynomial ring. -/
@[stacks 0AUG]
#check @RingHom.EssFiniteType.exists_localizedPolynomialQuotient
