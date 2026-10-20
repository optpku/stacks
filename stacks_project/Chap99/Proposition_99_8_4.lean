/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Representability

/-!
# Proposition 99.8.4

The proper-support Quot functor of a quasi-coherent module along a finitely
presented separated morphism of algebraic spaces is an algebraic space over
the base. It is locally of finite presentation when the module is finitely presented.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

universe u

/- Proposition 99.8.4 (1): the proper-support Quot functor is an algebraic space
for a finitely presented separated morphism and any quasi-coherent module. -/
@[stacks 09TU] #check (AlgebraicGeometry.AlgebraicSpace.Quot.quot_isAlgebraicSpaceOver :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (F : X.Modules) [F.IsQuasicoherent],
    IsAlgebraicSpaceOver (AlgebraicGeometry.AlgebraicSpace.Quot.quot f F))

/- Proposition 99.8.4 (2): when the quasi-coherent module is finitely presented,
the proper-support Quot functor is locally of finite presentation over the base. -/
@[stacks 09TU] #check
  (AlgebraicGeometry.AlgebraicSpace.Quot.quot_isLocallyOfFinitePresentationOver :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [FinitePresentation f] [Separated f] (F : X.Modules)
      [F.IsQuasicoherent] [F.IsFinitePresentation],
      IsLocallyOfFinitePresentationOver (AlgebraicGeometry.AlgebraicSpace.Quot.quot f F))
