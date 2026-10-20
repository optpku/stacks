/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.LocalEquality
import StacksCheckRecall

/-!
# Lemma 29.35.17

Morphisms to an unramified scheme that agree at a point and on the induced residue-field map agree
on an open neighborhood of that point.

@stack 04HB
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.35.17

Let `X` and `Y` be schemes over `S`, and let `f g : X ⟶ Y` be morphisms over `S`.
If `Y ⟶ S` is unramified, the morphisms have the same value at `x`, and their induced
residue-field maps at `x` agree, then they agree on an open neighborhood of `x`.
-/
@[stacks 04HB] #check
  (AlgebraicGeometry.Unramified.exists_open_eq_of_residueFieldMap_eq :
    ∀ {S X Y : Scheme.{u}} {fX : X ⟶ S} {fY : Y ⟶ S}
      {f g : X ⟶ Y} {x : X} {y : Y} [Unramified fY]
      (hf_over : f ≫ fY = fX) (hg_over : g ≫ fY = fX)
      (hfxy : f x = y) (hgxy : g x = y)
      (hres : (Scheme.residueFieldCongr hfxy).inv ≫ f.residueFieldMap x =
        (Scheme.residueFieldCongr hgxy).inv ≫ g.residueFieldMap x),
      ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g)
