/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor

/-!
# Derived tensor products of modules on schemes

This file exposes the K-flat monoidal structure on the derived category of module sheaves on a
scheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The derived category of module sheaves on a scheme carries the K-flat monoidal structure of
modules on its underlying ringed space. -/
noncomputable instance instDerivedMonoidalCategory (X : Scheme.{u})
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace] :
    MonoidalCategory (DerivedCategory X.Modules) :=
  RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace

end AlgebraicGeometry.Scheme.Modules
