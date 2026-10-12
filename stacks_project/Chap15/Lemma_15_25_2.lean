/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.PrimeLocalization
import StacksCheckRecall

/-!
# Lemma 15.25.2

@stack 053B

The prime-local finite-presentation criterion for flat finite-type algebras is owned by the
reusable finite-presentation API.
-/

@[expose] public section

/- Lemma 15.25.2: a flat finite-type algebra is finitely presented when all prime-local base
changes are finitely presented and finitely many base-prime localizations detect equality. -/
@[stacks 053B "Lemma 15.25.2"]
#check @Algebra.FinitePresentation.ofFlatPrimeLocalizations
