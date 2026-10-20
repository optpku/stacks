/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SheafTorsor.Restriction

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/- Inverse image of fppf sheaves of groups along a morphism of schemes over the base. -/
#check (AlgebraicGeometry.SheafTorsors.inverseImageGrp :
  ∀ {U U' : Over S}, (U ⟶ U') →
    Sheaf (Scheme.fppfTopology.over U'.left) GrpCat.{u} ⥤
      Sheaf (Scheme.fppfTopology.over U.left) GrpCat.{u})
