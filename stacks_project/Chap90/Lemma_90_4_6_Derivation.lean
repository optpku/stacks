/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.DerivationRestriction

/-!
# Restriction of residue derivations along morphisms in `Ĉ_Λ`

A morphism `f` in `CompleteLocalAlgCat Λ k` induces a `k`-linear restriction map
`Derivation Λ S.carrier k →ₗ[k] Derivation Λ R.carrier k` by precomposition with the
underlying algebra map of `f`.
-/

@[expose] public section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (CompleteLocalAlgCat.Hom.mapDerivation :
  ∀ {R S : CompleteLocalAlgCat Λ k} (f : CompleteLocalAlgCat.Hom R S),
    Derivation Λ S.carrier k →ₗ[k] Derivation Λ R.carrier k)

#check (CompleteLocalAlgCat.Hom.mapDerivation_apply :
  ∀ {R S : CompleteLocalAlgCat Λ k} (f : CompleteLocalAlgCat.Hom R S)
    (D : Derivation Λ S.carrier k) (x : R.carrier),
    CompleteLocalAlgCat.Hom.mapDerivation f D x = D (f.hom x))
