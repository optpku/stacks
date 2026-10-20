/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GeneralLinear.FirstRow
public import Mathlib.Data.Complex.Basic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open GeneralLinear

variable (n : {n : ℕ // 1 ≤ n})

/- Exercise 111.37.5: for any integer `n ≥ 1`, `GeneralLinear.scheme ℂ (ULift (Fin (n.1 + 1)))`
is an affine scheme and `FirstRow.toProjectiveSpace ℂ n.1` is a surjective morphism to
`ProjectiveSpace.scheme ℂ n.1`. -/
@[stacks 02A1] #check (AlgebraicGeometry.GeneralLinear.FirstRow.toProjectiveSpace ℂ n.1 :
  Scheme.Hom (GeneralLinear.scheme ℂ (ULift (Fin (n.1 + 1)))) (ProjectiveSpace.scheme ℂ n.1))
#check (inferInstance : IsAffine (GeneralLinear.scheme ℂ (ULift (Fin (n.1 + 1)))))
#check (inferInstance : Surjective (FirstRow.toProjectiveSpace ℂ n.1))
