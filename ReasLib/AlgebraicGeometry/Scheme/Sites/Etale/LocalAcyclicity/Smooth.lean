/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalAcyclicity
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open CategoryTheory AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Smooth morphisms of schemes are universally locally acyclic. -/
instance UniversallyLocallyAcyclic.of_smooth {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] : UniversallyLocallyAcyclic f :=
  sorry

end AlgebraicGeometry.Scheme
