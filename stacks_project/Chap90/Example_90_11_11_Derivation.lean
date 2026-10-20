/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Derivation
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.ProrepresentableTangent

/-!
# Morphisms into square-zero extensions as derivations

A morphism `S ⟶ k[V]` compatible with residue augmentations corresponds to a
`Λ`-derivation `S → V`, via its infinitesimal component. The inverse adjoins
the derivation value to the canonical residue component.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Example 90.11.11: morphisms into finite square-zero extensions correspond to derivations. -/
#check (CompleteLocalAlgCat.homEquivDerivation :
  ∀ (S : CompleteLocalAlgCat Λ k) (V : Type u) [AddCommGroup V] [Module k V]
    [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V],
    (S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V)) ≃
      Derivation Λ S.carrier V)

#check (CategoryTheory.Functor.IsPredeformationFunctor.tangentSpaceEquivDerivation :
  ∀ (S : CompleteLocalAlgCat Λ k),
    CategoryTheory.Functor.IsPredeformationFunctor.tangentSpace
      (CompleteLocalAlgCat.restrictedCoyoneda S) ≃ Derivation Λ S.carrier k)
