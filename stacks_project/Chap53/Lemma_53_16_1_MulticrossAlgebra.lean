/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.PowerSeries.Multicross

@[expose] public section

universe u

#check (Multicross.algebraMap_mem :
  ∀ {k : Type u} [Field k] {n : ℕ} (c : k),
    algebraMap k (Fin n → PowerSeries k) c ∈ Multicross.ring k n)

#check (Multicross.instAlgebra :
  ∀ {k : Type u} [Field k] {n : ℕ}, Algebra k (Multicross.ring k n))

#check (Multicross.algebraMap_apply :
  ∀ {k : Type u} [Field k] {n : ℕ} (c : k) (i : Fin n),
    (algebraMap k (Multicross.ring k n) c : Fin n → PowerSeries k) i = PowerSeries.C c)
