/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Galois.Topology
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Topology

universe u

section

variable {X : Scheme.{u}} [ConnectedSpace X] (xbar : GeometricPoint X)

/- Theorem 64.27.2 (Grothendieck) -/
@[stacks 03VF]
#check
  (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber_nhds_one_has_basis_stabilizers xbar :
    (nhds (1 : Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).HasBasis
        (fun _ : (Σ Y : FiniteEtale X,
          (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar).obj Y) ↦ True)
        (fun p ↦ MulAction.stabilizer
          (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)) p.2) ∧
      ∀ (Y : FiniteEtale X)
        (y : (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar).obj Y),
        IsOpen
          (MulAction.stabilizer
            (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)) y :
            Set (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))))

/- Theorem 64.27.2 (Grothendieck) (2): with the Aut topology of (1),
π₁(X, xbar) is a profinite group. -/
@[stacks 03VF]
#check
  (AlgebraicGeometry.Scheme.GeometricPoint.etaleFundamentalGroup X xbar : ProfiniteGrp)

/- Theorem 64.27.2 (Grothendieck) (3): Y/X ↦ F_xbar(Y) with its natural
continuous action is an equivalence FiniteEtale X ≌ finite discrete
continuous π₁-sets. -/
@[stacks 03VF]
#check
  (CategoryTheory.PreGaloisCategory.functorToContAction_isEquivalence
    (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar) :
    (CategoryTheory.PreGaloisCategory.functorToContAction
      (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)).IsEquivalence)

end
