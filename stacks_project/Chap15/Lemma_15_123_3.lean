/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Determinant.Composition
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.123.3

The source statement is the contravariant composition law for determinant maps.  The reusable
owner is `CochainComplex.Determinant.map_comp`; it already packages the three admissibility
conditions and uses the canonical short-exact determinant comparisons from ReasLib.

@stack 0FJL
-/

open CochainComplex.Determinant

/- Lemma 15.123.3: `det(b) ∘ det(a) = det(b ∘ a)` as maps on determinant lines. -/
@[stacks 0FJL "Lemma 15.123.3: composition of determinant maps"]
#check @CochainComplex.Determinant.map_comp

#check @CochainComplex.Determinant.IsAdmissible.comp
#check @CochainComplex.Determinant.line
#check @CochainComplex.Determinant.map

end
