/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Diagonal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equality for Morphisms to an Unramified Scheme

Two morphisms over a common base to a scheme unramified over that base agree on an open
neighborhood when they have the same value and induce the same residue-field map at a point.
If the target morphism is also separated and the source scheme is connected, this agreement
forces the morphisms to be equal globally.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

variable {S X Y : Scheme.{u}} {fX : X ⟶ S} {fY : Y ⟶ S}
variable {f g : X ⟶ Y} {x : X} {y : Y}

/-- Two morphisms over a common base to an unramified scheme that agree at a point and on the
induced residue-field map agree on an open neighborhood of that point. -/
@[stacks 04HB]
theorem Unramified.exists_open_eq_of_residueFieldMap_eq
    [Unramified fY]
    (hf_over : f ≫ fY = fX) (hg_over : g ≫ fY = fX)
    (hfxy : f x = y) (hgxy : g x = y)
    (hres :
      (Scheme.residueFieldCongr hfxy).inv ≫ f.residueFieldMap x =
        (Scheme.residueFieldCongr hgxy).inv ≫ g.residueFieldMap x) :
    ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g := by
  sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.Unramified

/-- Two morphisms from a connected scheme to a scheme unramified and separated over a common
base are equal if they agree at one point and induce the same residue-field map there. -/
@[stacks 024V]
theorem eq_of_residueFieldMap_eq {S X Y : Scheme.{u}} (π : X ⟶ S)
    [Unramified π] [IsSeparated π] (p : Y ⟶ S) [ConnectedSpace Y]
    (f g : Y ⟶ X) (hf_over : f ≫ π = p) (hg_over : g ≫ π = p)
    (y : Y) (x : X) (hfy : f y = x) (hgy : g y = x)
    (hκ : (Scheme.residueFieldCongr hfy).inv ≫ f.residueFieldMap y =
      (Scheme.residueFieldCongr hgy).inv ≫ g.residueFieldMap y) : f = g := sorry

end AlgebraicGeometry.Unramified
