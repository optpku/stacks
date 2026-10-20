/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GeneralLinear.GroupScheme

open CategoryTheory
open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.GeneralLinear.groupScheme :
  (R : Type u) → [CommRing R] → (I : Type u) → [Fintype I] → [DecidableEq I] →
    Grp (Over (Spec (CommRingCat.of R))))
