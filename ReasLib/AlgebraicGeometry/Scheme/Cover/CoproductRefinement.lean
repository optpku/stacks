/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Finite coproduct Zariski refinements

Finite coproduct Zariski refinement properties of scheme covers.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.Cover

/-- A cover of a scheme `T` has a finite coproduct Zariski refinement if some
finite open cover `𝒱` refines it and `Sigma.desc 𝒱.f` is an isomorphism, so `T`
is the coproduct of the members of `𝒱`. -/
def HasFiniteCoproductZariskiRefinement {T : Scheme.{u}} {K : Precoverage Scheme.{u}}
    (𝒰 : T.Cover.{v} K) : Prop :=
  ∃ (𝒱 : T.OpenCover.{u}) (_ : 𝒱.toPreZeroHypercover.Hom 𝒰.toPreZeroHypercover),
    Finite 𝒱.I₀ ∧ IsIso (Sigma.desc 𝒱.f)

/-- A finite coproduct Zariski refinement consists of a finite open cover,
a pre-`0`-hypercover refinement, and an isomorphism from its coproduct to the
target. -/
theorem hasFiniteCoproductZariskiRefinement_iff {T : Scheme.{u}}
    {K : Precoverage Scheme.{u}} (𝒰 : T.Cover.{v} K) :
    𝒰.HasFiniteCoproductZariskiRefinement ↔
      ∃ (𝒱 : T.OpenCover.{u}) (f : 𝒱.toPreZeroHypercover.Hom 𝒰.toPreZeroHypercover),
        Finite 𝒱.I₀ ∧ IsIso (Sigma.desc 𝒱.f) := sorry

end AlgebraicGeometry.Scheme.Cover
