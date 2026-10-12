/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_29_1_RingedSite
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.21.1: let `S` be a scheme and let `X` be an algebraic space over `S`.
The rule `U ↦ Γ(U, 𝒪_U)` is `structurePresheaf X`, with values
`RingCat.of Γ(U.left.left, ⊤)` by `structurePresheaf_obj`, and is a sheaf of rings
on `smallEtaleTopology X`. -/
@[stacks 03G6] #check
  (AlgebraicGeometry.AlgebraicSpace.structurePresheaf_isSheaf :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      Presheaf.IsSheaf (smallEtaleTopology X) (structurePresheaf X))
