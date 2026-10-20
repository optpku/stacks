/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree

/-!
# Base change of universally bounded fibres

Universally bounded fibres of a morphism from a scheme to an algebraic space are
preserved by base change along a representable morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A fixed numerical bound on fibre degrees is preserved by represented base change. -/
theorem degreesOfFibresBoundedBy_baseChange {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {U : Over S} (g : Y ⟶ X) (hg : yoneda.relativelyRepresentable g)
    (f : ofOver U ⟶ X) {n : ℕ} (hf : degreesOfFibresBoundedBy f n) :
    degreesOfFibresBoundedBy (hg.fst f) n :=
  sorry

/-- Universally bounded fibres of a morphism from a scheme to an algebraic space remain
universally bounded after base change along a representable morphism of algebraic spaces. -/
@[stacks 03JN]
theorem universallyBoundedFibres_baseChange {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {U : Over S} (g : Y ⟶ X) (hg : yoneda.relativelyRepresentable g)
    (f : ofOver U ⟶ X) (hf : universallyBoundedFibres f) :
    universallyBoundedFibres (hg.fst f) := by
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, degreesOfFibresBoundedBy_baseChange g hg f hn⟩

/-- Universal fibre boundedness is preserved along a pullback square of algebraic spaces
whose apex and lower source are schemes. -/
theorem universallyBoundedFibres_of_isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {U P : Over S} {g : Y ⟶ X} {f : ofOver U ⟶ X} {πY : ofOver P ⟶ Y}
    {πU : ofOver P ⟶ ofOver U} (sq : IsPullback πY πU g f)
    (hf : universallyBoundedFibres f) : universallyBoundedFibres πY :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
