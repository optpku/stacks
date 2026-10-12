/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Definition_82_32_1_Degree
import StacksCheckRecall

/-!
# Degree of zero-cycle classes on proper algebraic spaces over a field
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Definition 82.32.1: Let k be a field. Let p : X ⟶ Spec k be a proper morphism
of algebraic spaces. The degree of a zero-cycle class on X is the composite
p_* : CH_0(X) ⟶ CH_0(Spec k) ⟶ ℤ of proper pushforward on Chow groups
(Lemma 82.16.3) with the natural isomorphism CH_0(Spec k) ≃ ℤ sending
[Spec k] to 1. Notation: deg(α). -/
@[stacks 0ESG]
#check (Hom.chowDegree :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Proper (toBase X)],
    Hom.chowGroup (toBase X) (fun _ ↦ (0 : ℤ)) 0 →+ ℤ)

end AlgebraicGeometry.AlgebraicSpace
