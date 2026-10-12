/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Lemma_82_4_3_Length
public import stacks_project.Chap82.Lemma_82_4_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Definition 82.4.2: let `S` be a scheme and let `X` be an algebraic space over `S`.
Let `F` be a quasi-coherent `𝒪_X`-module. Let `x ∈ |X|`. Let `d : ℕ∞`. We say `F`
has length `d` at `x` if the equivalent conditions of Lemma 82.4.1 are satisfied. -/
@[stacks 0EE2]
#check (hasLengthAt :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, X.Modules → Points X → ℕ∞ → Prop)

#check lengthAt_tfae
#check hasLengthAt_iff
#check exists_lengthAtGeometricPoint_iff
#check exists_lengthOnEtaleChart_iff_forall
