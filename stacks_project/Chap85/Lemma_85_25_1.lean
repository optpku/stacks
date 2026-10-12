/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_25_1_Comparison
import StacksCheckRecall

/-!
# Lemma 85.25.1

Let `U` be a simplicial object of `LCCat` and let `a : U ⟶ X` be an
augmentation. There is a commutative square of morphisms of topoi
`Sh((LC_qc / U)_total) ⟶ Sh(U_Zar)` over `Sh(LC_qc / X) ⟶ Sh(X)`.
-/

@[expose] public section

/- Lemma 85.25.1
Let `U` be a simplicial object of `LCCat` and let `a : U ⟶ X` be an
augmentation. There is a commutative square of morphisms of topoi
`Sh((LC_qc / U)_total) ⟶ Sh(U_Zar)` over `Sh(LC_qc / X) ⟶ Sh(X)`, whose left vertical
arrow `a_qc` is the Section 85.21 slice augmentation `sliceAugmentationTopos qcTopology`,
whose right vertical arrow `a` is the Lemma 85.2.8 Zariski augmentation
`augmentationMorphism (toTopCatAugmentation a)`, and whose horizontal arrows are
`h = qcOpensOverTotalTopos` presented by `V ↦ V / U_n` and
`h₋₁ = opensOverQcTopos` presented by `V ↦ V / X`. -/
@[stacks 0DAF] #check @LCCat.qcOpensOver_inverseImage_comp
