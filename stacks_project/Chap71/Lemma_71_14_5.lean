module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap71.Lemma_71_14_3_RelativelyAmple

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

/-- Lemma 71.14.5: let `h : V ⟶ U` be a surjective étale morphism of affine
schemes. Let `X` be an algebraic space over `U` via `f : X ⟶ U`, and let `L`
be an invertible `𝒪_X`-module. Let `Y = V ×_U X` and let `N` be the pullback of
`L` to `Y`. Then `RelativelyAmple f L` if and only if `N` is ample on `Y / V`,
that is `RelativelyAmple (pullback.snd f h)
((Modules.pullback (pullback.fst f h)).obj L)`. -/
@[stacks 0D35]
theorem RelativelyAmple.iff_baseChange_of_surjectiveEtaleAffine
    {S : Scheme.{u}} {U V X : AlgebraicSpace S} [IsAffine U] [IsAffine V]
    (h : V ⟶ U) [Etale h] [Surjective h] (f : X ⟶ U) (L : X.Modules)
    [isInvertibleObject L] :
    RelativelyAmple f L ↔
      RelativelyAmple (pullback.snd f h)
        ((Modules.pullback (pullback.fst f h)).obj L) :=
  sorry

/-- Relative ampleness of the pullback of an invertible module along a
surjective étale morphism of affine schemes implies relative ampleness over
the original affine base. -/
theorem RelativelyAmple.of_baseChange_of_surjectiveEtaleAffine
    {S : Scheme.{u}} {U V X : AlgebraicSpace S} [IsAffine U] [IsAffine V]
    (h : V ⟶ U) [Etale h] [Surjective h] (f : X ⟶ U) (L : X.Modules)
    [isInvertibleObject L]
    [RelativelyAmple (pullback.snd f h)
      ((Modules.pullback (pullback.fst f h)).obj L)] :
    RelativelyAmple f L :=
  sorry

/-- Relative ampleness of the pullback of an invertible module around a
cartesian square whose base change is a surjective étale morphism of affine
algebraic spaces implies relative ampleness of the original module. -/
theorem RelativelyAmple.of_isPullback_of_surjectiveEtaleAffine
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {L : X.Modules} [IsAffine Y] [IsAffine Y']
    [Etale g] [Surjective g] [isInvertibleObject L] (sq : IsPullback g' f' f g)
    (hN : RelativelyAmple f' ((Modules.pullback g').obj L)) :
    RelativelyAmple f L :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
