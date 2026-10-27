/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Defs.Filter
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FieldPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

/-!
# Relative flatness and associated points of algebraic spaces

For a finite-type quasicoherent module and a locally finite-type morphism, flatness at
the relative associated points of a fibre specializing to a point implies flatness at
that point. The converse holds for decent source and target spaces.

Flatness along the closed fibre of a local base implies global relative flatness
when every point of the relative assassin specializes into that fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- A finite-type quasicoherent module on an algebraic space locally of finite type over
another algebraic space is flat at a point if it is flat at every relatively weakly
associated point in the same set-theoretic fibre that specializes to that point. -/
@[stacks 0CWL]
theorem flatOverAt_of_relativeWeakAss_specializingTo
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (x : Points X)
    (h : ∀ x' ∈ relativeWeakAss f ℱ ∩ Points.map f ⁻¹' {Points.map f x},
      Specializes x' x → flatOverAt ℱ f x') :
    flatOverAt ℱ f x :=
  sorry

/-- For a locally finite-type morphism of decent algebraic spaces, a finite-type
quasicoherent module flat at a point is flat at every relatively weakly associated point
in the same set-theoretic fibre that specializes to it. -/
@[stacks 0CWL]
theorem relativeWeakAss_specializingTo_of_flatOverAt
    {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    {x x' : Points X} (hflat : flatOverAt ℱ f x)
    (hx'_ass_fiber : x' ∈ relativeWeakAss f ℱ ∩ Points.map f ⁻¹' {Points.map f x})
    (hspec : Specializes x' x) :
    flatOverAt ℱ f x' :=
  sorry

/-- For a locally finite-type morphism of decent algebraic spaces, a finite-type
quasicoherent module is flat at a point if and only if it is flat at every relatively
weakly associated point in the same set-theoretic fibre that specializes to it. -/
theorem flatOverAt_iff_relativeWeakAss_specializingTo
    {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (x : Points X) :
    flatOverAt ℱ f x ↔
      ∀ x' ∈ relativeWeakAss f ℱ ∩ Points.map f ⁻¹' {Points.map f x},
        Specializes x' x → flatOverAt ℱ f x' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin

/-- A finite-type quasicoherent module on an algebraic space locally of finite type over a
local scheme is flat over the base if it is flat along the closed fibre and every point of
its relative assassin specializes to a point of that fibre. -/
@[stacks 0CWM]
theorem flatOver_of_specializesTo_closedFiber
    {S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)] {X : AlgebraicSpace S}
    [LocallyOfFiniteType (SchemeRealization.toBase X)] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S)
    (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤))
    (h_ass : ∀ x ∈ relativeAssassin (SchemeRealization.toBase X) ℱ,
      ∃ z : Points X, Points.base z = s ∧ Specializes x z)
    (h_flat : ∀ z : Points X, Points.base z = s →
      flatOverAt ℱ (SchemeRealization.toBase X) z) :
    flatOver ℱ (SchemeRealization.toBase X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin
