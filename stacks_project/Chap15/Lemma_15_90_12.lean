/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.H0.OfModule
import StacksCheckRecall

/-!
# Recovery from canonical formal gluing

The reusable owner exposes the explicit degree-zero unit and its natural isomorphism under the
flat quotient-preserving hypotheses.

@stack 05EM
-/

@[expose] public section

/- Lemma 15.90.12 (Stacks 05EM): for a finite principal-open family, flatness and bijectivity on
the quotient by the cover ideal make `H⁰` a left quasi-inverse to canonical formal gluing. -/
@[stacks 05EM] #check
  @LocalizedModule.Away.FormalGluing.h0LeftQuasiInverseIso_of_flat_of_quotientMap_bijective

#check @LocalizedModule.Away.FormalGluing.h0Unit_bijective_of_flat_of_quotientMap_bijective
#check @LocalizedModule.Away.FormalGluing.h0UnitCompNatIso_of_flat_of_quotientMap_bijective
