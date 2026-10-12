/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.Lemma_88_15_8_RigFlat
import StacksCheckRecall

@[expose] public section

/- Definition 88.15.4: let `φ : A →+* B` be a continuous ring homomorphism
between adic Noetherian topological rings, i.e., `φ` is an arrow of
`WAdm^{Noeth}`. We say `φ` is rig-flat if `φ` is adic, topologically of finite
type, and for all `f ∈ A` the induced map of completed principal localizations
`completedPrincipalLocalization I f ⟶ completedPrincipalLocalization (I.map φ) (φ f)`
is naively rig-flat (Definition 88.15.2). -/
@[stacks 0GGP] #check RingHom.RigFlat
