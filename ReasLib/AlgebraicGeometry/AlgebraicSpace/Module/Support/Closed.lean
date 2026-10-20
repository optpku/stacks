/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.FiniteType

/-!
# Closed support of modules on algebraic spaces

The closed support is the closure of the étale-site support. For finite-type
quasi-coherent modules it equals the support and commutes with pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The closed support of an `𝒪_X`-module is the topological closure of its
étale-site support. -/
def closedSupport {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    Closeds (Points X) :=
  Closeds.closure (moduleSupport F)

/-- For a finite-type quasi-coherent `𝒪_X`-module, the closed support is the
étale-site support. -/
@[simp]
theorem coe_closedSupport {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] :
    (closedSupport F : Set (Points X)) = moduleSupport F :=
  sorry

/-- Pullback of a finite-type quasi-coherent `𝒪_X`-module carries closed support
to inverse image along the induced map on points. -/
theorem closedSupport_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (f : Y ⟶ X) :
    closedSupport ((pullback f).obj F) =
      (closedSupport F).preimage (Points.continuous_map f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
