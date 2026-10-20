/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap47.Lemma_47_6_3
public import ReasLib.Algebra.Module.MatlisDuality.IdealDuality
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 47.6.4 (1): Restriction to the `I`-annihilated submodule identifies its
dual with the quotient of the dual by `I`. -/
@[stacks 08Z0] #check
  (LinearMap.IsInjectiveHull.quotientDualToDualTorsion_bijective :
    ∀ (R : Type u) (E : Type v) (M : Type w) [CommRing R] [IsLocalRing R]
      [IsArtinianRing R] [AddCommGroup E] [Module R E] [Module.Injective R E]
      [AddCommGroup M] [Module R M] [Module.Finite R M]
      {ι : IsLocalRing.ResidueField R →ₗ[R] E} (hι : ι.IsInjectiveHull) (I : Ideal R),
      Function.Bijective (Module.IdealDuality.quotientDualToDualTorsion R E I M))

/- Lemma 47.6.4 (2): Precomposition with `M ⟶ M / IM` identifies the dual of
`M / IM` with the `I`-annihilated submodule of the dual of `M`. -/
@[stacks 08Z0] #check
  (LinearMap.IsInjectiveHull.dualQuotientToTorsion_bijective :
    ∀ (R : Type u) (E : Type v) (M : Type w) [CommRing R] [IsLocalRing R]
      [IsArtinianRing R] [AddCommGroup E] [Module R E] [Module.Injective R E]
      [AddCommGroup M] [Module R M] [Module.Finite R M]
      {ι : IsLocalRing.ResidueField R →ₗ[R] E} (hι : ι.IsInjectiveHull) (I : Ideal R),
      Function.Bijective (Module.IdealDuality.dualQuotientToTorsion R E I M))
