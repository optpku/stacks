/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.Principal.Colon
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.28.1 (Tag 05K8): a subideal of a principal ideal is recovered from its colon ideal.

@stack 05K8
-/

@[stacks 05K8 "principal-ideal factorization owner"]
#check @Ideal.IsPrincipal.eq_mul_colon_of_le

@[stacks 05K8 "principal-ideal factorization criterion"]
#check @Ideal.IsPrincipal.eq_mul_colon_iff_le

@[stacks 05K8 "multiplication-colon residuation"]
#check @Ideal.mul_le_iff_le_colon

@[stacks 05K8 "principal generator factorization"]
#check @Ideal.eq_span_singleton_mul
