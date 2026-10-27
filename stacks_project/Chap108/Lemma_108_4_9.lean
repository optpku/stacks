/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.TensorPower
import StacksCheckRecall

/-! # Tensor-power numerical substacks of coherent sheaves -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open scoped Bicategory

universe u

/- Lemma 108.4.9 (1): the numerical substack for a finite list of perfect derived
modules is open for every prescribed function on its integral tensor-power indices. -/
@[stacks 0DNE] #check
  (AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.instOpenImmersionTensorPower :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [FinitePresentation f] [Separated f] {r : ℕ}
      (E : Fin r → ModuleDerived X) (hE : ∀ i, ModuleDerived.IsPerfect (E i))
      (P : tensorPowerIndex r → ℤ),
      CohStack.OpenImmersion
        (CohStack.Numerical.ι f (tensorPowerFamily E) P
          (fun n ↦ isPerfect_tensorPowerFamily E hE n)))

/- Lemma 108.4.9 (2): the numerical substack for a finite list of perfect derived
modules is closed for every prescribed function on its integral tensor-power indices. -/
@[stacks 0DNE] #check
  (AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.instClosedImmersionTensorPower :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [FinitePresentation f] [Separated f] {r : ℕ}
      (E : Fin r → ModuleDerived X) (hE : ∀ i, ModuleDerived.IsPerfect (E i))
      (P : tensorPowerIndex r → ℤ),
      CohStack.Hom.ClosedImmersion
        (CohStack.Numerical.ι f (tensorPowerFamily E) P
          (fun n ↦ isPerfect_tensorPowerFamily E hE n)))
