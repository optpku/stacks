/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

variable
  (k : Type u) [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (L : X.Modules) [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L]
  (Z : X.IdealSheafData) (d : ℕ)
  (hZdim : topologicalKrullDim Z.subscheme = d)
  [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]

/- Definition 33.45.10: the degree of a closed subscheme with respect to an ample invertible
module is its self-intersection number in the dimension of the closed subscheme. -/
@[stacks 0BEW] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.degree_def k f L Z hZdim :
    AlgebraicGeometry.Scheme.Modules.Intersection.degree k f L Z hZdim =
      AlgebraicGeometry.Scheme.Modules.Intersection.selfNumber k f Z hZdim L)
