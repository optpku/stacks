/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatScheme

/-!
# Category of schemes flat over Artinian local algebras

Compatibility checks for the flat-scheme category and its base projection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (FlatSchemeCat Λ k : Type (u + 1))
#check (FlatSchemeCat.of (Λ := Λ) (k := k) :
  ∀ (A : ArtinianLocalAlgCat Λ k) (X : Scheme.{u})
    (structureHom : X ⟶ Spec (CommRingCat.of A.carrier)),
    AlgebraicGeometry.Flat structureHom → FlatSchemeCat Λ k)
#check (FlatSchemeCat.Hom.of (Λ := Λ) (k := k) :
  ∀ {src tgt : FlatSchemeCat Λ k} (baseHom : src.base ⟶ tgt.base)
    (schemeHom : tgt.scheme ⟶ src.scheme),
    IsPullback schemeHom tgt.structureHom src.structureHom (FlatSchemeCat.specMap baseHom) →
      FlatSchemeCat.Hom src tgt)
#check (FlatSchemeCat.forget Λ k : FlatSchemeCat Λ k ⥤ ArtinianLocalAlgCat Λ k)
