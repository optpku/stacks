/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.GeometricRegularity
import StacksCheckRecall

/-!
# Definition 10.166.2

@stack 0382
-/

@[expose] public section

open scoped TensorProduct

universe u v

variable {k : Type u} {R : Type v}
variable [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R]

/- Definition 10.166.2: a Noetherian algebra over a field `k` is geometrically regular over `k`
when `Algebra.IsGeometricallyRegular` holds, i.e. when condition (2) of Lemma 10.166.1 holds. -/
@[stacks 0382]
#check (Algebra.IsGeometricallyRegular k R : Prop)

#check (Algebra.IsGeometricallyRegular.iff_tensorRegular :
  Algebra.IsGeometricallyRegular k R ↔
    ∀ (K : Type (max u v)) [Field K] [Algebra k K]
      [FiniteDimensional k K] [IsPurelyInseparable k K],
      IsRegularRing (K ⊗[k] R))
