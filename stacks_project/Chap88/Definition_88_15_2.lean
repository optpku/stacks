module

public import stacks_project.Chap88.Lemma_88_15_8_RigFlat
import StacksCheckRecall

@[expose] public section

/- Definition 88.15.2: let `φ : A →+* B` be a continuous ring homomorphism
between adic Noetherian topological rings, i.e., `φ` is an arrow of
`WAdm^{Noeth}`. We say `φ` is naively rig-flat if `φ` is adic, topologically
of finite type, and satisfies the equivalent conditions of Lemma 88.15.1. -/
@[stacks 0GGM] #check RingHom.NaiveRigFlat
