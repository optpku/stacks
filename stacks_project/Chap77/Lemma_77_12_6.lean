module

public import stacks_project.Chap77.Lemma_77_12_6_Concentration
public import stacks_project.Chap77.Lemma_77_12_6_SpecialFiber
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.12.6: in Situation 77.12.1, with `K` as in Lemma 77.12.2, the
closed subset `X_0 ⊂ |X|` of points lying over `Spec(A_n) ⊂ Spec(A)` is
contained in an open subspace `W ⊂ X` on which `H^i(K)|_W` vanishes for
`i ≠ 0`, the sheaf `ℱ = H^0(K)|_W` is of finite presentation, and
`ℱ n = ℱ ⊗_{𝒪_X} 𝒪_{X_n}` via the canonical stage comparison. -/
@[stacks 0CX9] #check ProperFlatFormalSystem.existsOpen_coheratorLimit_concentrated_finitePresentation
