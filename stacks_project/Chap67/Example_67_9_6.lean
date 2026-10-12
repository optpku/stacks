/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Example_67_9_6_Space
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation

universe u

/- Example 67.9.6: for a characteristic-zero field `k`, the structure morphism
`p : 𝔸¹_k / ℤ ⟶ Spec(k)` of the algebraic space from Spaces, Example 65.14.8 is
universally closed. -/
@[stacks 03IV] #check instUniversallyClosed_structureHom
