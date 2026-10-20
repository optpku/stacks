/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.SmashAway
import StacksCheckRecall

/-!
# Smash-away factorization of a morphism étale outside a closed subset

A locally finite-type morphism of algebraic spaces that is étale off a closed
subset `T` factors through a locally finite-type morphism which is an
isomorphism over the complement of `T` and an isomorphism on completions along
`T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/- Lemma 88.25.7: Let `S` be a scheme. Let `X` be a locally Noetherian algebraic
space over `S` and let `T ⊂ Points X` be a closed subset. Let `f : X' ⟶ X` be a
morphism of algebraic spaces which is locally of finite type and étale outside of
`T`. There exists a factorization `X' ⟶ X'' ⟶ X` of `f` such that `X'' ⟶ X` is
locally of finite type, `X'' ⟶ X` is an isomorphism over `X \ T`, and
`X'_/T ⟶ X''_/T` is an isomorphism.

Étale outside `T` means `Etale (openInverseImageTo f (openComplementι X T))`.
The induced map of completions `X'_/T ⟶ X''_/T` is `mapOverHom T h f g w`. -/
@[stacks 0AR9] #check (AlgebraicGeometry.AlgebraicSpace.completionAlong.exists_smashAwayFactor :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) (f : X' ⟶ X)
    [LocallyOfFiniteType f]
    (hf : Etale (openInverseImageTo f (openComplementι X T))),
    ∃ (X'' : AlgebraicSpace S) (g : X' ⟶ X'') (h : X'' ⟶ X) (w : g ≫ h = f)
      (_ : LocallyOfFiniteType h) (_ : IsIsoOverOpen h (openComplementι X T)),
      IsIso (mapOverHom T h f g w))

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
