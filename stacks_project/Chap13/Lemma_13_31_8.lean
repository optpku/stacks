/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.KInjective.SequentialLimit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.31.8

The reusable statement is a sequential inverse-system theorem: it records the
termwise K-injectivity, degreewise limit hypotheses, and split-epimorphic
successor maps without exposing the proof's coordinate-level Hom-complex
construction.
-/

/- Lemma 13.31.8 (Stacks 070L): the inverse limit of a termwise split-epic
sequential system of K-injective cochain complexes is K-injective. -/
@[stacks 070L] #check @CategoryTheory.SequentialInverseSystem.isKInjective_limit_of_termwiseSplitEpi
