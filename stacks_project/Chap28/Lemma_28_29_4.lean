/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.AffineOpen
import StacksCheckRecall

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 28.29.4: for a quasi-separated scheme, an arbitrary point and finitely many chosen
generic points of pairwise distinct irreducible components lie in a common affine open. -/
@[stacks 01ZX] #check
  (AlgebraicGeometry.Scheme.exists_affineOpen_containing_point_and_genericPoints :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [QuasiSeparatedSpace X.carrier] {n : ℕ}
      (x : X) (Z : Fin n → irreducibleComponents X) (η : Fin n → X),
      Pairwise (fun i j ↦ Z i ≠ Z j) →
        (∀ i, IsGenericPoint (η i) (Z i : Set X)) →
          ∃ U : X.affineOpens,
            x ∈ ((U : X.Opens) : Set X) ∧ ∀ i, η i ∈ ((U : X.Opens) : Set X))
