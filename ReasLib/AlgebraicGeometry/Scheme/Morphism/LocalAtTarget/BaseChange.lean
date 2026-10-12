/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic

/-!
# Base change of properties local on the target

This file gives base-change criteria for morphism properties of schemes that
are local on the target in the standard Grothendieck topologies.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace CategoryTheory.MorphismProperty.IsLocalAtTarget

variable {P : MorphismProperty Scheme.{u}}
  {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {i : X' ⟶ X} {f' : X' ⟶ Y'}

/-- An fpqc-local morphism property on the target is preserved by pullback along a flat
morphism. -/
theorem of_isPullback_fpqc
    [P.IsLocalAtTarget Scheme.fpqcPrecoverage] [Flat g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' := sorry

/-- An fppf-local morphism property on the target is preserved by pullback along a flat,
locally finitely presented morphism. -/
theorem of_isPullback_fppf
    [P.IsLocalAtTarget Scheme.fppfPrecoverage] [Flat g]
    [LocallyOfFinitePresentation g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' := sorry

/-- A syntomic-local morphism property on the target is preserved by pullback along a syntomic
morphism. -/
theorem of_isPullback_syntomic
    [P.IsLocalAtTarget Scheme.bigSyntomicPrecoverage] [Syntomic g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' := sorry

/-- A smooth-local morphism property on the target is preserved by pullback along a smooth
morphism. -/
theorem of_isPullback_smooth
    [P.IsLocalAtTarget Scheme.bigSmoothPrecoverage] [Smooth g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' := sorry

/-- An étale-local morphism property on the target is preserved by pullback along an étale
morphism. -/
theorem of_isPullback_etale
    [P.IsLocalAtTarget Scheme.etalePrecoverage] [Etale g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' := sorry

/-- A Zariski-local morphism property on the target is preserved by pullback along an open
immersion. -/
theorem of_isPullback_zariski
    [P.IsLocalAtTarget Scheme.zariskiPrecoverage] [IsOpenImmersion g]
    (sq : IsPullback i f' f g) (hf : P f) : P f' := sorry

end CategoryTheory.MorphismProperty.IsLocalAtTarget
