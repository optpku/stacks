/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.CartesianOver

open CategoryTheory AlgebraicGeometry
open CategoryTheory.SimplicialObject

universe u v

/- Lemma 85.27.4: A cartesian morphism of simplicial schemes over the Čech nerve
of `f : X ⟶ S` determines a descent datum with component `Y₀` over `X` and comparison
isomorphism induced by the two degree-one face maps. -/
@[stacks 024B] #check (AlgebraicGeometry.Scheme.DescentData.ofCartesianHom :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) {Y : SimplicialObject Scheme.{u}}
    (π : Y ⟶ f.simplicialScheme) [IsCartesian π],
    AlgebraicGeometry.Scheme.DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
