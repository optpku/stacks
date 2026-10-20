/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.Fibered.InSets.Slice

/-!
# Categories fibred in groupoids over schemes

The standard universe-pinned groupoid fibration bicategory over `Over S`, together
with its canonical slice fibrations. Representability properties live in their
own source-facing layer and are not required for these basic data.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Categories fibred in groupoids over the big fppf site `(Sch/S)_fppf`. -/
abbrev GroupoidsOver (S : Scheme.{u}) :=
  FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)

/-- The canonical slice of a scheme over `S`, as an object of `GroupoidsOver S`. -/
abbrev GroupoidsOver.slice {S : Scheme.{u}} (U : Over S) : GroupoidsOver S :=
  FiberedCategoryOver.Groupoids.slice U

namespace GroupoidsOver

/-- The object of `(Sch/V)_fppf` over `U` associated to a morphism `f : U ⟶ V`
of schemes over `S`. -/
def sliceHomObject {S U V : Scheme.{u}} (hU : U ⟶ S) (hV : V ⟶ S)
    (f : U ⟶ V) (h_over : f ≫ hV = hU) :
    (GroupoidsOver.slice (Over.mk hV)).total :=
  Over.mk (Over.homMk f h_over : Over.mk hU ⟶ Over.mk hV)

/-- The slice object of `f` lies over `U ⟶ S`. -/
theorem sliceHomObject_over {S U V : Scheme.{u}} (hU : U ⟶ S) (hV : V ⟶ S)
    (f : U ⟶ V) (h_over : f ≫ hV = hU) :
    (GroupoidsOver.slice (Over.mk hV)).p.obj (sliceHomObject hU hV f h_over) =
      Over.mk hU :=
  sorry

/-- `sliceHomObject hU hV f h_over` is the over-object associated to `f`. -/
theorem sliceHomObject_spec {S U V : Scheme.{u}} (hU : U ⟶ S) (hV : V ⟶ S)
    (f : U ⟶ V) (h_over : f ≫ hV = hU) :
    sliceHomObject hU hV f h_over =
      Over.mk (Over.homMk f h_over : Over.mk hU ⟶ Over.mk hV) :=
  sorry

end GroupoidsOver

end AlgebraicGeometry
