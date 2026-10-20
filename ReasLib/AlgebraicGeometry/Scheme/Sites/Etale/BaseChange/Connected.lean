/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Map
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Set
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Every canonical morphism on strict henselizations induced at a geometric point
has geometrically connected fibres. -/
def hasGeometricallyConnectedStrictHenselFibers {X S : Scheme.{u}}
    (f : X ⟶ S) : Prop :=
  ∀ x : GeometricPoint X, GeometricallyConnected (StrictHenselization.map f x)

/-- Geometrically connected strict-henselization fibres are equivalent to geometric
connectedness of the canonical induced morphism at every geometric point. -/
theorem hasGeometricallyConnectedStrictHenselFibers_iff {X S : Scheme.{u}}
    (f : X ⟶ S) :
    hasGeometricallyConnectedStrictHenselFibers f ↔
      ∀ x : GeometricPoint X, GeometricallyConnected (StrictHenselization.map f x) := sorry

/-- A morphism with geometrically connected strict-henselization fibres induces a
geometrically connected morphism on strict henselizations at each geometric point. -/
theorem hasGeometricallyConnectedStrictHenselFibers_apply {X S : Scheme.{u}}
    {f : X ⟶ S} (h_fib : hasGeometricallyConnectedStrictHenselFibers f)
    (x : GeometricPoint X) :
    GeometricallyConnected (StrictHenselization.map f x) := sorry

/-- Flat inverse image commutes with quasi-compact, quasi-separated direct image of
set-valued small étale sheaves when the induced morphisms on strict henselizations
at all geometric points have geometrically connected fibres. -/
theorem etaleSetBaseChange_of_geometricallyConnectedStrictHenselFibers
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    [Flat f] [QuasiCompact g] [QuasiSeparated g]
    (h_cart : IsPullback h e f g)
    (h_fib : hasGeometricallyConnectedStrictHenselFibers f)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    IsIso (BaseChange.setMap f h e g h_cart F) := sorry

end AlgebraicGeometry.Scheme.Etale
