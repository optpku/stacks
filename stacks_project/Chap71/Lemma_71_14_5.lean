/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative.Descent
import StacksCheckRecall

/-!
# Lemma 71.14.5

Relative ampleness of an invertible module on an algebraic space over an
affine scheme descends along a surjective étale morphism of affine schemes.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 71.14.5: let `h : V ⟶ U` be a surjective étale morphism of affine
schemes. Let `X` be an algebraic space over `U` via `f : X ⟶ U`, and let `L`
be an invertible `𝒪_X`-module. Let `Y = V ×_U X` and let `N` be the pullback of
`L` to `Y`. Then `RelativelyAmple f L` if and only if `N` is ample on `Y / V`,
that is `RelativelyAmple (pullback.snd f h)
((Modules.pullback (pullback.fst f h)).obj L)`. -/
@[stacks 0D35] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.iff_baseChange_of_surjectiveEtaleAffine :
    ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S} [IsAffine U] [IsAffine V]
    (h : V ⟶ U) [Etale h] [Surjective h] (f : X ⟶ U) (L : X.Modules)
    [isInvertibleObject L],
    RelativelyAmple f L ↔
      RelativelyAmple (pullback.snd f h)
        ((Modules.pullback (pullback.fst f h)).obj L))

/- Relative ampleness of the pullback of an invertible module along a
surjective étale morphism of affine schemes implies relative ampleness over
the original affine base. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.of_baseChange_of_surjectiveEtaleAffine :
    ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S} [IsAffine U] [IsAffine V]
    (h : V ⟶ U) [Etale h] [Surjective h] (f : X ⟶ U) (L : X.Modules)
    [isInvertibleObject L]
    [RelativelyAmple (pullback.snd f h)
      ((Modules.pullback (pullback.fst f h)).obj L)],
    RelativelyAmple f L)

/- Relative ampleness of the pullback of an invertible module around a
cartesian square whose base change is a surjective étale morphism of affine
algebraic spaces implies relative ampleness of the original module. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.of_isPullback_of_surjectiveEtaleAffine :
    ∀ {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {L : X.Modules} [IsAffine Y] [IsAffine Y']
    [Etale g] [Surjective g] [isInvertibleObject L] (sq : IsPullback g' f' f g)
    (hN : RelativelyAmple f' ((Modules.pullback g').obj L)),
    RelativelyAmple f L)

end AlgebraicGeometry.AlgebraicSpace
