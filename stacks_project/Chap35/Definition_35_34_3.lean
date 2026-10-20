/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.DescentData
import StacksCheckRecall

open CategoryTheory

universe u v

/-
Definition 35.34.3: For a family of scheme morphisms `f i : X i ⟶ S`, descent data consist of
schemes over the `X i`, pairwise pullback isomorphisms satisfying the triple-overlap cocycle,
with morphisms given by compatible componentwise maps.
-/
@[stacks 023W] #check (@AlgebraicGeometry.Scheme.DescentData :
  {I : Type v} → {S : AlgebraicGeometry.Scheme.{u}} →
    (X : I → AlgebraicGeometry.Scheme.{u}) →
      ((i : I) → X i ⟶ S) → Type (max (max v (u + 1)) u))

#check @AlgebraicGeometry.Scheme.DescentData.ofObj
#check @AlgebraicGeometry.Scheme.DescentData.Chosen
#check @AlgebraicGeometry.Scheme.DescentData.Chosen.ofIso
#check @AlgebraicGeometry.Scheme.DescentData.Chosen.iso
#check @AlgebraicGeometry.Scheme.DescentData.Chosen.cocycle
#check @AlgebraicGeometry.Scheme.DescentData.Chosen.hom_comm
#check @AlgebraicGeometry.Scheme.DescentData.Chosen.equivalence
