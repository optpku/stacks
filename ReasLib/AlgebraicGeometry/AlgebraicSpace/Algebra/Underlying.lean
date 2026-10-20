/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal

/-!
# Underlying modules of quasi-coherent algebras

This file exposes the sheaf and module underlying a quasi-coherent algebra on an algebraic space, together
with the map on underlying modules induced by an algebra morphism.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The `𝒪_X`-module underlying a quasi-coherent `𝒪_X`-algebra. -/
abbrev underlyingModule (A : X.QcAlgebraUnder) : X.Modules :=
  (Modules.ofCommModules X).obj <|
    (restrictionAlong.{u + 1, u, u, u} A.obj.hom).obj
    (unitModule (smallEtaleTopology X) (sheaf A))

/-- The map of underlying `𝒪_X`-modules induced by a morphism of quasi-coherent
`𝒪_X`-algebras. -/
abbrev underlyingModuleMap {A B : X.QcAlgebraUnder} (f : A ⟶ B) :
    underlyingModule A ⟶ underlyingModule B := by
  apply (Modules.ofCommModules X).map
  let alpha : sheaf A ⟶ sheaf B := ((forget X).map f).right
  let raw :
      SheafOfModules.unit (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (sheaf A)) ⟶
        (restrictionAlong.{u + 1, u, u, u} ((forget X).map f).right).obj
          (SheafOfModules.unit (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (sheaf B))) := by
    let rawPush :=
      SheafOfModules.unitToPushforwardObjUnit.{u, u, u + 1, u + 1, u}
        (SheafOfModules.ChangeOfRings.homOverId.{u + 1, u, u}
          (ringSheafMap.{u + 1, u, u} (J := smallEtaleTopology X) alpha))
    exact rawPush ≫
      (SheafOfModules.ChangeOfRings.pushforwardIso.{u + 1, u, u, u}
        (ringSheafMap.{u + 1, u, u} (J := smallEtaleTopology X) alpha)).hom.app
        (SheafOfModules.unit (ringSheaf.{u + 1, u, u} (smallEtaleTopology X) (sheaf B)))
  have hcomp : A.obj.hom ≫ ((forget X).map f).right = B.obj.hom := by
    simpa using (((forget X).map f).w).symm
  let raw :
      (restrictionAlong.{u + 1, u, u, u} A.obj.hom).obj
          (unitModule (smallEtaleTopology X) (sheaf A)) ⟶
        (restrictionAlong.{u + 1, u, u, u} (A.obj.hom ≫ ((forget X).map f).right)).obj
          (unitModule (smallEtaleTopology X) (sheaf B)) :=
    (restrictionAlong.{u + 1, u, u, u} A.obj.hom).map raw
  simpa using hcomp ▸ raw

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
