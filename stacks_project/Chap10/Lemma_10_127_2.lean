/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.Over.FinitePresentation.Directed
import StacksCheckRecall

/-!
# Directed finite-presentation models

@stack 00QN

The shared owner is universe-polymorphic and keeps both the directed presentation and the
surjective-transition finite-type refinement available outside Chapter 10.
-/

@[expose] public section

/- Lemma 10.127.2 (Tag 00QN) (1): every algebra is a directed colimit of finitely presented
algebras over its base. -/
@[stacks 00QN "(1)"]
#check @CommAlgCat.Over.FinitePresentation.exists_directedSystem

/- Lemma 10.127.2 (Tag 00QN) (2): for a finite-type algebra, the transition maps may all be
chosen surjective. -/
@[stacks 00QN "(2)"]
#check @CommAlgCat.Over.FinitePresentation.exists_surjectiveSystem_of_finiteType
