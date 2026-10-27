/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.LowerShriek.Affine
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ModulesOnCategory

universe u

/- Lemma 104.8.3: For an algebraic stack and a flat-fppf derived object with
quasi-coherent cohomology, the canonical derived tensor comparison map of its
lower-shriek image is an isomorphism for every morphism of affine objects. -/
@[stacks 0H15] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfLowerShriek_affineComparison_isIso :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
      (K : DerivedQCohFlatFppf X) {x x' : affineSite X} (f : x ⟶ x'),
      IsIso
        ((chaoticComparison.{u + 1, u, u} (affineStructureSheaf X) f).app
          ((restrictLowerShriekToAffine X).obj K)))
