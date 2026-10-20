module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap87.Lemma_87_14_4_Completion
public import stacks_project.Chap88.Definition_88_20_1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.RigEtale
import StacksCheckRecall

/-!
# Rig-étale morphisms of completions

If a morphism of algebraic spaces is locally of finite type, the source is
completed along the closed preimage of a closed subset, and the comparison of
open complements is étale, then the induced morphism of formal completions is
rig-étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

/- Lemma 88.23.9: if `X` is locally Noetherian, `f : X' ⟶ X` is locally of
finite type, and the comparison
`openInverseImageTo f (OpenSubspace.ofOpensι T.compl)` of the open complements of
`T` is étale, then `completionAlong.map f T` is rig-étale. -/
@[stacks 0AR2] #check (AlgebraicGeometry.AlgebraicSpace.rigEtale_completionAlongMap :
    ∀ {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [AlgebraicSpace.LocallyOfFiniteType f] (T : Closeds (Points X))
    [AlgebraicSpace.Etale (openInverseImageTo f (OpenSubspace.ofOpensι T.compl))],
    FormalAlgebraicSpace.RigEtale (completionAlong.map f T))
