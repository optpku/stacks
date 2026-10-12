/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.H0.Adjunction
import StacksCheckRecall

/-!
# The canonical formal-gluing adjunction

The reusable owner constructs the unit and counit explicitly and packages their triangle
identities as the adjunction between canonical formal gluing and degree-zero sections.

@stack 0H77
-/

@[expose] public section

/- Lemma 15.90.11 (Stacks 0H77): canonical formal gluing is left adjoint to degree-zero
sections. -/
@[stacks 0H77] #check
  @LocalizedModule.Away.FormalGluing.h0Adjunction

#check @LocalizedModule.Away.FormalGluing.h0AdjunctionUnit
#check @LocalizedModule.Away.FormalGluing.h0CounitNatTrans
