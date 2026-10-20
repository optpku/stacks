/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.ValuativeCriterion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

universe u

/- Example 67.41.6 (1): the structure morphism of the quadratic Galois twist
of the doubled-origin affine line is quasi-compact. -/
@[stacks 03KI] #check
  (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.instQuasiCompact_spaceStructureHom :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
      (hdeg : Module.finrank k k' = 2),
      AlgebraicGeometry.AlgebraicSpace.QuasiCompact (spaceStructureHom k k' hdeg))

/- Example 67.41.6 (2): the structure morphism of the quadratic Galois twist
of the doubled-origin affine line is universally closed. -/
@[stacks 03KI] #check
  (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.instUniversallyClosed_spaceStructureHom :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
      (hdeg : Module.finrank k k' = 2),
      AlgebraicGeometry.AlgebraicSpace.UniversallyClosed (spaceStructureHom k k' hdeg))

/- Example 67.41.6 (3): the valuative square `Spec(k⸨X⸩) ⟶ X` over
`Spec(k⟦X⟧) ⟶ 𝔸¹_k` has no dotted lift. -/
@[stacks 03KI] #check
  (AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.not_hasLift :
    ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
      (hdeg : Module.finrank k k' = 2), ¬ (valuativeCommSq k k' hdeg).HasLift)

