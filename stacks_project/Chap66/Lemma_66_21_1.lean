/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.21.1: let `S` be a scheme and let `X` be an algebraic space over `S`.
The rule `U ↦ Γ(U, 𝒪_U)` is `SmallEtale.structurePresheaf X`, the composite
of the opposite underlying scheme functor `(SmallEtale.toScheme X).op` with
`Scheme.Γ` and the forgetful functor from commutative rings to rings. It is a
sheaf of rings on `SmallEtale.topology X`. -/
@[stacks 03G6] #check
  (AlgebraicGeometry.AlgebraicSpace.SmallEtale.structurePresheaf_isSheaf :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      Presheaf.IsSheaf (AlgebraicGeometry.AlgebraicSpace.SmallEtale.topology X)
        (AlgebraicGeometry.AlgebraicSpace.SmallEtale.structurePresheaf X))
