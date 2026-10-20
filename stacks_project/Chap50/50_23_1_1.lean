/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- 50.23.1.1: The degree-`p` Gysin morphism from relative forms on the closed subscheme
cut out by an ordered family of equations to degree-`c` local cohomology. -/
@[stacks 0G84] #check
  (@AlgebraicGeometry.Scheme.DeRham.Gysin.map :
    {X S : Scheme.{u}} → (q : X ⟶ S) → {c : ℕ} →
      (fs : Fin c → Γ(X, ⊤)) → (p : ℕ) →
      AlgebraicGeometry.Scheme.DeRham.Gysin.source q fs p ⟶
        (ModuleCech.LocalCohomology.cohomologyFunctor fs).obj
          (AlgebraicGeometry.Scheme.DeRham.Gysin.relativeForm q (p + c)))
