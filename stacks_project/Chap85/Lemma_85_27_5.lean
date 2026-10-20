/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.CartesianOver.Equivalence

open CategoryTheory AlgebraicGeometry

universe u v

/- Lemma 85.27.5: The degree-zero descent construction is an equivalence between
cartesian simplicial schemes over the Čech nerve and descent data relative to a
morphism of schemes. -/
@[stacks 024C] #check (AlgebraicGeometry.Scheme.DescentData.ofCartesianOverEquivalence :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    CategoryTheory.SimplicialObject.CartesianOver f.simplicialScheme ≌
      AlgebraicGeometry.Scheme.DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
