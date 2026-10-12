/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.Definition_88_20_1_Ring
public import stacks_project.Chap88.Definition_88_18_1_Ring

@[expose] public section

universe u

namespace Algebra.RigEtale

/-- Lemma 88.8.3: Let `A` be a Noetherian ring and let `I` be an ideal. Let `B`
be an object of (88.2.0.2). If `B` is rig-étale over `(A, I)`, then `B` is
rig-smooth over `(A, I)`. -/
@[stacks 0GB1]
instance toRigSmooth {A : Type u} [CommRing A] {I : Ideal A} {B : Type u}
    [CommRing B] [Algebra A B] [RigEtale I B] : RigSmooth I B := sorry

end Algebra.RigEtale
