/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.PrincipalTorsion
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

/- Lemma 52.3.1: for a scheme `X`, a global section `f`, and an inverse system `F`
whose positive stages are quasi-coherent, the stepwise short exact, power short exact,
divisible power-kernel, and torsion-free power-quotient conditions are equivalent. -/
@[stacks 0EH9] #check (AlgebraicGeometry.Scheme.Modules.PrincipalTorsion.conditions_tfae :
  ∀ {X : Scheme.{u}} (f : RingedSpace.globalSectionsRing X.toRingedSpace)
    (F : SequentialInverseSystem X.Modules),
    (∀ n : ℕ, 1 ≤ n → (F.obj (op n)).IsQuasicoherent) →
      List.TFAE [
        CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsPresented f F,
        CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsPowerPresented f F,
        CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsKernelPresented f F,
        CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsQuotientPresented f F])
