/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Relative
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.7.6

Finite presentation of the relative fibre-product module is recalled from the relative
pullback-adjunction API.

@stack 08KP
-/

/- Lemma 15.7.6: componentwise finite presentation and relative flatness, together with a
flat-then-finitely-presented factorization of `B' → D'`, imply finite presentation of the
fibre-product module. -/
@[stacks 08KP "Lemma 15.7.6: finite presentation after relative pullback"]
#check @FiberProductBaseChangeSituation.relativeRightAdjoint_finitePresentation_of_factorization

end
