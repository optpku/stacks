/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk

/-!
# Geometric residue-field fibers of module sheaves

The residue-field fiber of a module sheaf at a geometric point is the tensor product of the
residue field of the étale local ring with the module stalk.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The residue-field fiber `κ(xbar) ⊗[𝒪_{X, xbar}] F_xbar` of an `𝒪_X`-module at a geometric
point. -/
abbrev fiber {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    (F : X.Modules) : Type u :=
  IsLocalRing.ResidueField (etaleLocalRing X xbar) ⊗[etaleLocalRing X xbar]
    (stalkModuleCat xbar F)

/-- The residue-field fiber is the tensor product of the residue field of the étale local ring
with the étale module stalk. -/
theorem fiber_def {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)
    (F : X.Modules) :
    fiber xbar F =
      IsLocalRing.ResidueField (etaleLocalRing X xbar) ⊗[etaleLocalRing X xbar]
        (stalkModuleCat xbar F) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
