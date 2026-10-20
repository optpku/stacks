/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.RingedSite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.RingedComparison

/-! # Ringed total sites of a simplicial algebraic space

The two total structure sheaves are the actual global-section sheaves.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open CategoryTheory.SimplicialObject

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.etaleTotalStructureSheaf :
  ∀ {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S)),
    Sheaf (spacesEtaleTotalTopology U) RingCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.fppfTotalStructureSheaf :
  ∀ {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S)),
    Sheaf (sliceTotalTopology (fppfTopology S) U) RingCat.{u})
