/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap88.Lemma_88_23_10

/-!
# Rig-surjectivity of the completed relative diagonal

If a morphism of algebraic spaces is separated and locally of finite type,
the source is completed along the closed preimage of a closed subset, and the
comparison of open complements is a monomorphism, then the relative diagonal of
the induced morphism of formal completions is rig-surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Completing the source of a locally of finite type morphism into a locally
Noetherian algebraic space along the closed preimage of `T` yields a locally
Noetherian formal algebraic space. -/
instance instIsLocallyNoetherian_completionAlong_preimage_locallyOfFiniteType
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} [IsLocallyNoetherian X]
    (f : X' ⟶ X) [AlgebraicSpace.LocallyOfFiniteType f] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsLocallyNoetherian
      (completionAlong X' (T.preimage (Points.continuous_map f))) :=
  sorry

/-- The fibre product of completions of a morphism of algebraic spaces along a
closed subset is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_pullback_completionAlongMap
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace
      (pullback (completionAlong.map f T) (completionAlong.map f T)) :=
  sorry

/-- If `X` is locally Noetherian and `f` is locally of finite type, then the
fibre product of the completions of `f` along `T` is a locally Noetherian
formal algebraic space. -/
instance instIsLocallyNoetherian_pullback_completionAlongMap
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} [IsLocallyNoetherian X]
    (f : X' ⟶ X) [AlgebraicSpace.LocallyOfFiniteType f] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsLocallyNoetherian
      (pullback (completionAlong.map f T) (completionAlong.map f T)) :=
  sorry

/-- The relative diagonal of `completionAlong.map f T` is locally of finite type
when `f` is locally of finite type. -/
instance instLocallyOfFiniteType_diagonal_completionAlongMap
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X)
    [AlgebraicSpace.LocallyOfFiniteType f] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.LocallyOfFiniteType
      (pullback.diagonal (completionAlong.map f T)) :=
  sorry

/-- Lemma 88.23.11: if `X` is locally Noetherian, `f : X' ⟶ X` is separated and
locally of finite type, and the comparison
`openInverseImageTo f (OpenSubspace.ofOpensι T.compl)` of the open complements of
`T` is a monomorphism, then `pullback.diagonal (completionAlong.map f T)` is
rig-surjective. -/
@[stacks 0GDI, instance]
instance rigSurjective_diagonal_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [Separated f] [AlgebraicSpace.LocallyOfFiniteType f] (T : Closeds (Points X))
    [Mono (openInverseImageTo f (OpenSubspace.ofOpensι T.compl))] :
    FormalAlgebraicSpace.RigSurjective
      (pullback.diagonal (completionAlong.map f T)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
