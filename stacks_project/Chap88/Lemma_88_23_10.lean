module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap88.Definition_88_21_1
public import stacks_project.Chap88.Lemma_88_23_1

/-!
# Proper surjective morphisms of completions

If a morphism of algebraic spaces is proper, the source is completed along the
closed preimage of a closed subset, and the comparison of open complements is
surjective, then the induced morphism of formal completions is rig-surjective.
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

/-- Completing the source of a proper morphism into a locally Noetherian
algebraic space along the closed preimage of `T` yields a locally Noetherian
formal algebraic space. -/
instance instIsLocallyNoetherian_completionAlong_preimage {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X) [Proper f]
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsLocallyNoetherian
      (completionAlong X' (T.preimage (Points.continuous_map f))) :=
  sorry

/-- Lemma 88.23.10: if `X` is locally Noetherian, `f : X' ⟶ X` is proper, and
the comparison `openInverseImageTo f (OpenSubspace.ofOpensι T.compl)` of the
open complements of `T` is surjective, then `completionAlong.map f T` is
rig-surjective. -/
@[stacks 0AQW, instance]
instance rigSurjective_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [Proper f] (T : Closeds (Points X))
    [Surjective (openInverseImageTo f (OpenSubspace.ofOpensι T.compl))] :
    FormalAlgebraicSpace.RigSurjective (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
