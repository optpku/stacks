/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.CategoryTheory.Galois.Topology
public import ReasLib.Topology.Algebra.OpenSubgroup
public import stacks_project.Chap58.Theorem_58_6_2_Fiber

@[expose] public section

open CategoryTheory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry
open Topology

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [ConnectedSpace X] (xbar : GeometricPoint X)
    {Y : FiniteEtale X}

/- Definition 64.27.1 -/
@[stacks 03VE] #check
  (OpenSubgroup.stabilizer (Aut (standardFiniteEtaleFiber xbar)) :
    (y : (standardFiniteEtaleFiber xbar).obj Y) →
      OpenSubgroup (Aut (standardFiniteEtaleFiber xbar)))

#check
  (OpenSubgroup.stabilizer_toSubgroup (Aut (standardFiniteEtaleFiber xbar)) :
    ∀ (y : (standardFiniteEtaleFiber xbar).obj Y),
      (OpenSubgroup.stabilizer (Aut (standardFiniteEtaleFiber xbar)) y).toSubgroup =
        MulAction.stabilizer (Aut (standardFiniteEtaleFiber xbar)) y)

#check
  (OpenSubgroup.mem_stabilizer (Aut (standardFiniteEtaleFiber xbar)) :
    ∀ (y : (standardFiniteEtaleFiber xbar).obj Y)
      {g : Aut (standardFiniteEtaleFiber xbar)},
      g ∈ OpenSubgroup.stabilizer (Aut (standardFiniteEtaleFiber xbar)) y ↔ g • y = y)

end AlgebraicGeometry.Scheme
