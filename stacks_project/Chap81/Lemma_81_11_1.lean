/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing.MorphismProperties
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 81.11.1 (1): In Situation 81.10.6 the canonical glueing functor
restricts to an equivalence on algebraic spaces affine over `X`, with all three structure maps affine. -/
@[stacks 0AF4] #check
  (AlgebraicGeometry.AlgebraicSpace.FormalGlueing.affineOverFunctor_isEquivalence :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
      [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
      [IsFormalGlueing f i],
      (AlgebraicGeometry.AlgebraicSpace.FormalGlueing.affineOverFunctor f i).IsEquivalence)

/- Lemma 81.11.1 (2): In Situation 81.10.6 the canonical glueing functor
restricts to an equivalence on closed immersions over `X`, with all three structure maps closed immersions. -/
@[stacks 0AF4] #check
  (AlgebraicGeometry.AlgebraicSpace.FormalGlueing.closedImmersionOverFunctor_isEquivalence :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
      [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
      [IsFormalGlueing f i],
      (AlgebraicGeometry.AlgebraicSpace.FormalGlueing.closedImmersionOverFunctor f i).IsEquivalence)

/- Lemma 81.11.1 (3): In Situation 81.10.6 the canonical glueing functor
restricts to an equivalence on finite morphisms over `X`, with all three structure maps finite. -/
@[stacks 0AF4] #check
  (AlgebraicGeometry.AlgebraicSpace.FormalGlueing.finiteOverFunctor_isEquivalence :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
      [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
      [IsFormalGlueing f i],
      (AlgebraicGeometry.AlgebraicSpace.FormalGlueing.finiteOverFunctor f i).IsEquivalence)
