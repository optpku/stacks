/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.DerivationRestriction

/-!
# Surjectivity from injectivity of residue-derivation restriction

A morphism in `CompleteLocalAlgCat Λ k` is surjective whenever the induced restriction
map on `Λ`-derivations into the identified residue field `k` is injective.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.4.6: if `f : R ⟶ S` is a morphism in `Ĉ_Λ = CompleteLocalAlgCat Λ k` and the
restriction map `mapDerivation f : Derivation Λ S.carrier k → Derivation Λ R.carrier k` is
injective, then the underlying algebra map of `f` is surjective. -/
@[stacks 06SD] #check (CompleteLocalAlgCat.Hom.surjective_of_mapDerivation_injective :
  ∀ {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S),
    Function.Injective (CompleteLocalAlgCat.Hom.mapDerivation f) → Function.Surjective f.hom)
