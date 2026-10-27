/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.LowerShriek.QuasiCoherent

/-!
# Lemma 104.3.3

For a quasi-coherent module on the lisse-étale or flat-fppf site of an algebraic
stack, every cohomology sheaf of derived lower shriek is locally quasi-coherent
and has the flat base change property.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver

universe u

/- Lemma 104.3.3 (1): cohomology of derived lower shriek of a quasi-coherent
lisse-étale module is locally quasi-coherent and has flat base change. -/
@[stacks 07B3] #check
  (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriek.homology_mem_lqcohFbc :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X))
      [H.IsQuasicoherent] (p : ℤ),
      lqcohFbc X (lisseEtaleModuleLowerShriek.homology X H p))

/- Lemma 104.3.3 (2): cohomology of derived lower shriek of a quasi-coherent
flat-fppf module has locally quasi-coherent étale restriction with flat base change. -/
@[stacks 07B3] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriek.homology_mem_lqcohFbc :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (H : SheafOfModules.{u} (flatFppfStructureSheaf X))
      [H.IsQuasicoherent] (p : ℤ),
      FppfModules.lqcohFbc X (flatFppfModuleLowerShriek.homology X H p))
