/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number

/-!
# Degrees of closed subschemes

This leaf owns the degree of a closed subscheme with respect to an invertible
scheme module.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Intersection

/-- The degree of a closed subscheme with respect to an invertible module is its
self-intersection number in the dimension of that closed subscheme. -/
noncomputable def degree
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (L : X.Modules) [Invertible L]
    (Z : X.IdealSheafData) {d : ℕ}
    (hZdim : topologicalKrullDim Z.subscheme = d)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})] : ℚ :=
  selfNumber k f Z hZdim L

/-- The degree with respect to an invertible module is the corresponding self-intersection
number. -/
theorem degree_def
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (L : X.Modules) [Invertible L]
    (Z : X.IdealSheafData) {d : ℕ}
    (hZdim : topologicalKrullDim Z.subscheme = d)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})] :
    degree k f L Z hZdim = selfNumber k f Z hZdim L := rfl

end AlgebraicGeometry.Scheme.Modules.Intersection
