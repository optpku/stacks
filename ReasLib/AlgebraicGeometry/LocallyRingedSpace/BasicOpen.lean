/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic opens of locally ringed spaces

This leaf identifies basic-open membership with avoidance of the maximal ideal in a local stalk.
The invertible-restriction statement is already owned by `RingedSpace.isUnit_res_basicOpen`.
-/

@[expose] public section

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X : LocallyRingedSpace.{u}}

/-- A point of an open set lies in the basic open of a section exactly when its germ avoids the
maximal ideal of the local stalk ring. -/
@[stacks 01HZ]
theorem mem_basicOpen_iff_notMem_maximalIdeal
    {U : Opens X} (f : X.presheaf.obj (op U)) (x : U) :
    (x : X) ∈ X.toRingedSpace.basicOpen f ↔
      X.presheaf.germ U (x : X) x.2 f ∉
        IsLocalRing.maximalIdeal (X.presheaf.stalk (x : X)) := sorry

/-- The global-section specialization of `mem_basicOpen_iff_notMem_maximalIdeal`. -/
@[stacks 01HZ "global-section basic-open membership"]
theorem mem_basicOpen_top_iff_notMem_maximalIdeal
    (f : X.presheaf.obj (op ⊤)) (x : X) :
    x ∈ X.toRingedSpace.basicOpen f ↔
      X.presheaf.Γgerm x f ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := sorry

end AlgebraicGeometry.LocallyRingedSpace
