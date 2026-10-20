/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.AssociatedCycle.Etale
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 82.10.3: In Situation 82.2.1, let `f : X ⟶ Y` be an étale
morphism of good algebraic spaces over `B`. For an integral closed subspace `Z`
of `Y`, the flat pullback `f^*[Z]` is the locally finite unweighted sum of all
irreducible components of the scheme-theoretic inverse image of `Z`. By the
definition of flat pullback on an integral generator, this is the associated
cycle of `Z.inverseImageSubspace f` in the relative dimension of `Z`, expressed
below by its coefficient at every point of `X`. -/
@[stacks 0EPY] #check (AlgebraicGeometry.AlgebraicSpace.Hom.etalePullback_integral :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
    [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    [IsLocallyNoetherian X] (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Etale f] (hf : f ≫ pY = pX) (Z : ClosedSubspace Y)
    [IsIntegral Z.X] (ξ : genericPoints Z.X) (x : Points X),
    ClosedSubspace.associatedCycle (Z.inverseImageSubspace f)
        (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction pX δ)
        (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction pY δ (Points.map Z.ι ξ.1)) x =
      Set.indicator
        (Points.map (Z.inverseImageSubspace f).ι '' genericPoints (Z.inverseImageSubspace f).X)
        (fun _ ↦ (1 : ℤ)) x)
