/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Functor

/-!
# Smash-away factorization of a morphism étale outside a closed subset

A locally finite-type morphism into a locally Noetherian algebraic space that
is étale outside a closed subset factors through a morphism isomorphic over
the complement, while preserving the completion along the closed subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- A locally finite-type morphism `f : X' ⟶ X` into a locally Noetherian
algebraic space, étale outside a closed subset `T`, factors as `g ≫ h = f`,
where `h` is locally of finite type and an isomorphism over the complement of
`T`, and `g` induces an isomorphism on completions along the inverse images of
`T`. The induced morphism of completions is the canonical `mapOverHom T h f g w`.
-/
@[stacks 0AR9]
theorem exists_smashAwayFactor {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) (f : X' ⟶ X)
    [LocallyOfFiniteType f]
    (hf : Etale (openInverseImageTo f (openComplementι X T))) :
    ∃ (X'' : AlgebraicSpace S) (g : X' ⟶ X'') (h : X'' ⟶ X) (w : g ≫ h = f)
      (_ : LocallyOfFiniteType h) (_ : IsIsoOverOpen h (openComplementι X T)),
      IsIso (mapOverHom T h f g w) :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
