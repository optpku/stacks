/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.NaiveComparison.Explicit

/-!
# Standard-resolution comparison formulas
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicTopology
open CommRingCat.Under.CotangentComplex
open CommRingCat.Under.FreeAlgebra
open scoped Simplicial ZeroObject TensorProduct ChangeOfRings

universe u

noncomputable section

#check (CategoryTheory.CommRingCat.Under.CotangentComplex.standardFace :
  ∀ (A : CommRingCat.{u}) (B : Under A) {n : ℕ} (i : Fin (n + 2)),
    standardTerm A B (op ⦋n + 1⦌) ⟶ standardTerm A B (op ⦋n⦌))

#check (CategoryTheory.CommRingCat.Under.CotangentComplex.faceSub :
  ∀ (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋1⦌)).right),
    (standardTerm A B (op ⦋0⦌)).right)

#check (CategoryTheory.CommRingCat.Under.CotangentComplex.toNaive :
  ∀ (A : CommRingCat.{u}) (B : Under A),
    obj A B ⟶ selfNaiveComplex A B)
