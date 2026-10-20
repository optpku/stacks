/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Residue

/-!
# Residue algebra structure on the identified residue field

A residue identification `ResidueField R.carrier ≃ₐ[Λ] k` makes `k` into an `R`-algebra,
so that `Derivation Λ R.carrier k` is the space of `Λ`-derivations from `R` into `k`.
-/

@[expose] public section

open IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (CompleteLocalAlgCat.instAlgebraCarrier :
  ∀ R : CompleteLocalAlgCat Λ k, Algebra Λ R.carrier)

#check (CompleteLocalAlgCat.instIsLocalRingCarrier :
  ∀ R : CompleteLocalAlgCat Λ k, IsLocalRing R.carrier)

#check (CompleteLocalAlgCat.algebra_residue :
  ∀ R : CompleteLocalAlgCat Λ k, Algebra R.carrier k)

#check (CompleteLocalAlgCat.algebra_residue_algebraMap :
  ∀ R : CompleteLocalAlgCat Λ k,
    algebraMap R.carrier k = R.residueFieldIso.toAlgHom.toRingHom.comp (residue R.carrier))

#check (CompleteLocalAlgCat.isScalarTower_residue :
  ∀ R : CompleteLocalAlgCat Λ k, IsScalarTower Λ R.carrier k)
