/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.RigSurjective
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

/- Lemma 88.23.11: if `X` is locally Noetherian, `f : X' ⟶ X` is separated and
locally of finite type, and the comparison
`openInverseImageTo f (OpenSubspace.ofOpensι T.compl)` of the open complements of
`T` is a monomorphism, then `pullback.diagonal (completionAlong.map f T)` is
rig-surjective. -/
@[stacks 0GDI] #check
  (AlgebraicGeometry.AlgebraicSpace.rigSurjective_diagonal_completionAlongMap :
    ∀ {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [Separated f] [AlgebraicSpace.LocallyOfFiniteType f] (T : Closeds (Points X))
    [Mono (openInverseImageTo f (OpenSubspace.ofOpensι T.compl))],
    FormalAlgebraicSpace.RigSurjective
      (pullback.diagonal (completionAlong.map f T)))

end AlgebraicGeometry.AlgebraicSpace
