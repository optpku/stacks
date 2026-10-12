/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.FiniteType.Local
import StacksCheckRecall

@[expose] public section

/-!
# Dimension of Maximal Localizations

@stack 00OS
-/

/- Lemma 10.114.4 (Stacks tag `00OS`): if `S` is a finite-type `k`-algebra that is an
integral domain, then `ringKrullDim S` equals the Krull dimension of the localization at
every maximal ideal of `S`. -/
@[stacks 00OS]
#check @Algebra.FiniteType.krullDim_eq_localizationAtMaximal
