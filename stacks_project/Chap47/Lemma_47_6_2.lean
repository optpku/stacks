/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.MatlisDuality.Artinian
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 47.6.2 (1): Every finite module over an Artinian local ring is reflexive
relative to an injective hull of the residue field. -/
@[stacks 08YY] #check
  (Module.isReflexiveRelativeTo_of_injectiveHull :
    ∀ (R : Type u) (E : Type v) (M : Type w) [CommRing R] [IsLocalRing R]
      [IsArtinianRing R] [AddCommGroup E] [Module R E] [Module.Injective R E]
      [AddCommGroup M] [Module R M] [Module.Finite R M]
      (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull),
      Module.IsReflexiveRelativeTo R E M)

/- Lemma 47.6.2 (2): The canonical scalar-action homomorphism identifies an
Artinian local ring with the endomorphism ring of an injective hull of its residue field. -/
@[stacks 08YY] #check
  (Module.toModuleEnd_bijective_of_injectiveHull :
    ∀ (R : Type u) (E : Type v) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
      [AddCommGroup E] [Module R E] [Module.Injective R E]
      (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull),
      Function.Bijective (Module.toModuleEnd R E : R →+* Module.End R E))
