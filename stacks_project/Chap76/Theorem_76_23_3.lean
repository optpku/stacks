/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.FiberCriterion.FinitePresentation

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Theorem 76.23.3: Let S be a scheme, let f : X ⟶ Y and h : Y ⟶ Z be morphisms of
algebraic spaces over S, and let F be a quasi-coherent 𝒪_X-module. Assume X is locally of
finite presentation over Z, F is of finite presentation, and Y is locally of finite type
over Z. Let x ∈ |X|, with images y ∈ |Y| and z ∈ |Z|. If the geometric stalk of F at x is
nonzero, the following are equivalent:
(1) F is flat over Z at x and its restriction to the fibre over z is flat at x over the
fibre of Y over z;
(2) Y is flat over Z at y and F is flat over Y at x.
Moreover, the set of points where (1) and (2) hold is open in Supp(F).
Finite presentation supplies quasi-coherence, and membership in moduleSupport expresses
nonvanishing of the geometric stalk. -/
@[stacks 05X0] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAt_and_fiber_iff_of_finitePresentation :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z),
      [LocallyOfFinitePresentation (f ≫ h)] → [LocallyOfFiniteType h] →
      ∀ (F : X.Modules), [F.IsFinitePresentation] → ∀ (x : Points X),
      x ∈ moduleSupport F →
      ((flatOverAt F (f ≫ h) x ∧ flatOnFiberAt_field F f h x) ↔
        (FlatAt h (Points.map f x) ∧ flatOverAt F f x)))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isOpen_flatnessByFibersLocus :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z),
    [LocallyOfFinitePresentation (f ≫ h)] → [LocallyOfFiniteType h] →
    ∀ (F : X.Modules), [F.IsFinitePresentation] →
    IsOpen ((Subtype.val : moduleSupport F → Points X) ⁻¹' flatnessByFibersLocus F f h))
