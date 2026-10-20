/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Generation
import StacksCheckRecall

/-!
# Lemma 15.79.1 (0ATI)

@stack 0ATI

Generation of the perfect derived category by `R[0]` is owned by ReasLib. This chapter file keeps
only the direct official-label recalls.
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.79.1 (1) (0ATI): perfect objects form the saturated triangulated envelope of `R[0]`.
-/
@[stacks 0ATI "Lemma 15.79.1 (1)"]
#check @perfectObjectProperty_eq_objectGeneratedProperty_ring_single

/- Lemma 15.79.1 (2) (0ATI): `R[0]` is a classical generator of the perfect derived category. -/
@[stacks 0ATI "Lemma 15.79.1 (2)"]
#check @ring_single_isClassicalGenerator_in_perfectDerivedCategory

#check @PerfectDerived
#check @ringSingleInPerfectDerived

#print axioms ringSingleInPerfectDerived
