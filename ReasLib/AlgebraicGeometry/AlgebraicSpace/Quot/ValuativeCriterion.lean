/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver.ValuativeCriterion

/-!
# Existence in the valuative criterion for the Quot functor

The Quot functor of a finite-type quasi-coherent module on an algebraic space
proper and of finite presentation over the base satisfies the existence part
of the valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The Quot functor of a finite-type quasi-coherent module on a proper,
finitely presented algebraic space over `B` satisfies the existence part of
the valuative criterion. -/
instance instExistence (f : X ⟶ B) [FinitePresentation f] [Proper f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    SchemeOver.ValuativeCriterion.Existence (quot f F) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
