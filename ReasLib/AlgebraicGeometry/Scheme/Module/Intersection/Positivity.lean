/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number

/-!
# Positivity of intersection numbers

This file records positivity results for intersection numbers of ample invertible modules.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Intersection

/-- The intersection number of a dimension-`d` closed subscheme with `d` ample invertible
modules on a scheme proper over a field is strictly positive. -/
theorem number_pos_of_isAmple
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (Z : X.IdealSheafData) {d : ℕ}
    (hZdim : topologicalKrullDim Z.subscheme = d)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : Fin d → X.Modules) [∀ j : Fin d, Invertible (L j)] [∀ j : Fin d, IsAmple (L j)] :
    0 < number k f Z hZdim L := sorry

end AlgebraicGeometry.Scheme.Modules.Intersection
