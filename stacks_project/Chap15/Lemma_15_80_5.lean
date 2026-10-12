/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.StrongGenerator
import StacksCheckRecall

/-!
# Lemma 15.80.5 (0FXL)

@stack 0FXL
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.80.5 (0FXL): `R[0]` strongly generates the perfect derived category over a regular
ring of finite Krull dimension. -/
@[stacks 0FXL "Lemma 15.80.5"]
#check @ringSingleInPerfectDerived_isStrongGenerator
