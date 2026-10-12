/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap87.Lemma_87_14_4_Completion
public import stacks_project.Chap88.Definition_88_20_1

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

namespace AlgebraicGeometry.AlgebraicSpace

/-- The formal completion of an algebraic space along a closed subset is a
formal algebraic space. -/
instance instIsFormalAlgebraicSpace_completionAlong {S : Scheme.{u}}
    (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (completionAlong X T) :=
  sorry

/-- The formal completion of a locally Noetherian algebraic space along a closed
subset is a locally Noetherian formal algebraic space. -/
instance instIsLocallyNoetherian_completionAlong {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsLocallyNoetherian X] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsLocallyNoetherian (completionAlong X T) :=
  sorry

/-- Completing the source of a locally of finite type morphism into a locally
Noetherian algebraic space along the closed preimage of `T` yields a locally
Noetherian formal algebraic space. -/
instance instIsLocallyNoetherian_completionAlong_preimage_locallyOfFiniteType
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} [IsLocallyNoetherian X]
    (f : X' ⟶ X) [AlgebraicSpace.LocallyOfFiniteType f] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsLocallyNoetherian
      (completionAlong X' (T.preimage (Points.continuous_map f))) :=
  sorry

/-- Lemma 88.23.9: if `X` is locally Noetherian, `f : X' ⟶ X` is locally of
finite type, and the comparison
`openInverseImageTo f (OpenSubspace.ofOpensι T.compl)` of the open complements of
`T` is étale, then `completionAlong.map f T` is rig-étale. -/
@[stacks 0AR2, instance]
instance rigEtale_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [AlgebraicSpace.LocallyOfFiniteType f] (T : Closeds (Points X))
    [AlgebraicSpace.Etale (openInverseImageTo f (OpenSubspace.ofOpensι T.compl))] :
    FormalAlgebraicSpace.RigEtale (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
