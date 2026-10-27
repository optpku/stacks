/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChangeComparison

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.sectionOfMatching :
    ∀ {S : Scheme.{u}} {P Q : AlgebraicSpace S} (k : Q ⟶ P) (M : Q.Modules)
    (U : smallEtaleSite P),
    CanonicalTwists.AffineMatching k M U →
      ((Modules.pushforward k).obj M).val.obj (op U))

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.pointHom :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S},
    X.functorOfPoints.obj (op T) → (ofOver T ⟶ X))
