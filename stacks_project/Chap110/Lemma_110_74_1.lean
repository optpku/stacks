/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NonseparatedAlgebraization.FormalModule
public import ReasLib.AlgebraicGeometry.NonseparatedAlgebraization.Moduli

/-!
# Counterexamples to algebraization of coherent sheaves

Doubling the affine line over `PowerSeries k` shows that separatedness is necessary for
Grothendieck existence and for algebraicity of coherent-sheaf and Quot moduli.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 110.74.1 (1): proper-support coherent completion can fail to be an equivalence
when the structure morphism is not separated. -/
@[stacks 0ARF] #check
  (AlgebraicGeometry.NonseparatedAlgebraization.not_isEquivalence_coherentProperSupportCompletionFunctor :
    ∀ {k : Type u} [Field k],
      ¬ (AlgebraicGeometry.Scheme.Modules.coherentProperSupportCompletionFunctor :
          AlgebraicGeometry.Scheme.Modules.CoherentProperSupportOver
            (AlgebraicGeometry.NonseparatedAlgebraization.toSpec k) ⥤
          AlgebraicGeometry.Scheme.Modules.CoherentFormalProperSupportOver
            (AlgebraicGeometry.NonseparatedAlgebraization.toSpec k)
            (AlgebraicGeometry.NonseparatedAlgebraization.idealSheaf k)).IsEquivalence)

/- Lemma 110.74.1 (2): the coherent-sheaf stack can fail to be algebraic without
separatedness. -/
@[stacks 0ARF] #check
  (AlgebraicGeometry.NonseparatedAlgebraization.not_isAlgebraicStack :
    ∀ {k : Type u} [Field k],
      ¬ AlgebraicGeometry.AlgebraicSpace.CohStack.AlgebraicStack
        (AlgebraicGeometry.AlgebraicSpace.CohStack.toGroupoids
          (AlgebraicGeometry.NonseparatedAlgebraization.spaceHom k)))

/- Lemma 110.74.1 (3): the proper-support Quot functor of the structure sheaf can fail
to be an algebraic space without separatedness. -/
@[stacks 0ARF] #check
  (AlgebraicGeometry.NonseparatedAlgebraization.not_isAlgebraicSpaceOver_quot :
    ∀ {k : Type u} [Field k],
      ¬ AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpaceOver
        (AlgebraicGeometry.AlgebraicSpace.Quot.quot
          (AlgebraicGeometry.NonseparatedAlgebraization.spaceHom k)
          (SheafOfModules.unit
            (AlgebraicGeometry.AlgebraicSpace.structureSheaf
              (AlgebraicGeometry.NonseparatedAlgebraization.spaceX k)))))
