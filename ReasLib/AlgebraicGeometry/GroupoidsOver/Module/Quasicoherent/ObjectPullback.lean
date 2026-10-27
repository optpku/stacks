/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.ObjectPullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- A module sheaf on a category fibred in groupoids over the big fppf site is
quasi-coherent if and only if its pullback to the big fppf site of the scheme underlying
every object is quasi-coherent. -/
theorem isQuasicoherent_iff_objectPullback
    (F : SheafOfModules.{u} (structureSheaf X)) :
    F.IsQuasicoherent ↔
      ∀ x : X.total, ((objectPullback X x).obj F).IsQuasicoherent :=
  sorry

/-- Pullback of a quasi-coherent `𝒪_X`-module to `(Sch/U)_fppf` remains
quasi-coherent. -/
instance objectPullback_isQuasicoherent
    (F : SheafOfModules.{u} (structureSheaf X))
    [F.IsQuasicoherent] (x : X.total) :
    ((objectPullback X x).obj F).IsQuasicoherent :=
  sorry

/-- If every object pullback `x^* F` is quasi-coherent on `(Sch/U)_fppf`, then
`F` is quasi-coherent. -/
theorem isQuasicoherent_of_objectPullback
    (F : SheafOfModules.{u} (structureSheaf X))
    (h : ∀ x : X.total, ((objectPullback X x).obj F).IsQuasicoherent) :
    F.IsQuasicoherent :=
  sorry

end AlgebraicGeometry.GroupoidsOver
