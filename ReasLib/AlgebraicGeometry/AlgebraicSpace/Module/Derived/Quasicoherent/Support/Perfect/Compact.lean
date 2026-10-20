/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.CategoryTheory.Preadditive.CompactObject

/-!
# Compact and perfect supported quasicoherent complexes

Compact objects in `D_QCoh,T(𝒪_X)` on a quasi-compact and quasi-separated algebraic
space, for a closed subset `T` with quasi-compact complement, are characterized by
perfectness in `D(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn

/-- An object of `D_QCoh,T(𝒪_X)` on a quasi-compact and quasi-separated algebraic space,
for a closed subset `T` whose complement is quasi-compact, is compact if and only if its
underlying derived module is perfect. -/
theorem isCompactObject_iff_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (T : Closeds (Points X))
    (hT : IsCompact (T.compl : Set (Points X)))
    (E : SupportedOn X (T : Set (Points X))) :
    IsCompactObject E ↔ ModuleDerived.IsPerfect E.obj := sorry

/-- A perfect object of `D_QCoh,T(𝒪_X)` on a quasi-compact and quasi-separated algebraic
space, for a closed subset `T` whose complement is quasi-compact, is compact. -/
theorem isCompactObject_of_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (T : Closeds (Points X))
    (hT : IsCompact (T.compl : Set (Points X)))
    {E : SupportedOn X (T : Set (Points X))} (hE : ModuleDerived.IsPerfect E.obj) :
    IsCompactObject E :=
  (isCompactObject_iff_isPerfect T hT E).mpr hE

/-- A compact object of `D_QCoh,T(𝒪_X)` on a quasi-compact and quasi-separated algebraic
space, for a closed subset `T` whose complement is quasi-compact, has a perfect
underlying derived module. -/
theorem isPerfect_of_isCompactObject {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (T : Closeds (Points X))
    (hT : IsCompact (T.compl : Set (Points X)))
    {E : SupportedOn X (T : Set (Points X))} (hE : IsCompactObject E) :
    ModuleDerived.IsPerfect E.obj :=
  (isCompactObject_iff_isPerfect T hT E).mp hE

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn
