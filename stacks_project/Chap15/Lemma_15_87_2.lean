/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Milnor.ShortExact.Snake
import StacksCheckRecall

/-!
# Lemma 15.87.2

@stack 0H31
-/

@[expose] public section

/-
Lemma 15.87.2 (Stacks 0H31): a short exact sequence of inverse systems of abelian groups
induces the canonical six-term Milnor exact sequence
`lim A_i ⟶ lim B_i ⟶ lim C_i ⟶ R¹ lim A_i ⟶ R¹ lim B_i ⟶ R¹ lim C_i`.
The shared owner presents `R¹ lim` as `DerivedLimit.R1` and the connecting map as the
snake-lemma boundary of the canonical product/difference diagram.
-/

@[stacks 0H31] #check @CategoryTheory.ShortComplex.ShortExact.limitR1_exact
#check @CategoryTheory.ShortComplex.ShortExact.limitR1Connecting
#check @CategoryTheory.ShortComplex.ShortExact.limit_mono_map_f
#check @CategoryTheory.ShortComplex.ShortExact.r1_epi_map_g
#check @CategoryTheory.ShortComplex.ShortExact.limitR1SnakeInput
#check @CategoryTheory.ShortComplex.ShortExact.productRow
