/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal

/-!
# Descent of relatively ample modules on algebraic spaces

Relative ampleness of an invertible module on a morphism of algebraic spaces is
equivalent to relative ampleness of every pullback along an fpqc covering of the
target. Relative ampleness also descends along a surjective étale morphism of
affine algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits MonoidalCategory

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.RelativelyAmple

/-- An invertible module on a morphism of algebraic spaces is relatively ample if and
only if each of its canonical base changes along an fpqc covering family of the target
is relatively ample. -/
theorem iff_forall_baseChange_of_fpqcCovering
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules)
    [isInvertibleObject L] {ι : Type v} (family : ι → Over Y)
    (hfamily : FpqcCovering family) :
    RelativelyAmple f L ↔
      ∀ i, RelativelyAmple (pullback.snd f (family i).hom)
        ((Modules.pullback (pullback.fst f (family i).hom)).obj L) :=
  sorry

/-- An invertible module over an affine algebraic space is relatively ample if and
only if its canonical pullback along a surjective étale morphism from an affine
algebraic space is relatively ample. -/
@[stacks 0D35]
theorem iff_baseChange_of_surjectiveEtaleAffine
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
theorem of_baseChange_of_surjectiveEtaleAffine
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
theorem of_isPullback_of_surjectiveEtaleAffine
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {L : X.Modules} [IsAffine Y] [IsAffine Y']
    [Etale g] [Surjective g] [isInvertibleObject L] (sq : IsPullback g' f' f g)
    (hN : RelativelyAmple f' ((Modules.pullback g').obj L)) :
    RelativelyAmple f L :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativelyAmple
