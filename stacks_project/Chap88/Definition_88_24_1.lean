/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.Definition_88_24_1_Modification
import StacksCheckRecall

@[expose] public section

/- Definition 88.24.1: let `S` be a scheme, and let `f : X ⟶ Y` be a morphism
of locally Noetherian formal algebraic spaces over `S`. The morphism `f` is a
formal modification if it is proper in the sense of Formal Spaces,
Definition 87.31.1 (representable by algebraic spaces, with
`AlgebraicSpace.Proper` Yoneda pullbacks), rig-étale (`RigEtale`), and
rig-surjective (`RigSurjective`), and the relative diagonal
`Δ_f : X ⟶ X ×_Y X`, encoded as `diagonal f : X ⟶ pullback f f`, is
rig-surjective. -/
@[stacks 0GDK] #check AlgebraicGeometry.FormalAlgebraicSpace.FormalModification
