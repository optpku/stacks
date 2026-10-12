/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.RepresentableTorsor

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.GroupScheme.representableGroup :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (τ : AlgebraicGeometry.StandardTopology)
    (G : Grp (Over S)), Sheaf (τ.overTopology S) GrpCat)
