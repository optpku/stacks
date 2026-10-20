/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Unramified

/-- An unramified flat morphism of schemes is formally étale. -/
instance toFormallyEtale {X S : Scheme.{u}} (f : X ⟶ S) [Unramified f] [Flat f] :
    FormallyEtale f := sorry

end AlgebraicGeometry.Unramified
