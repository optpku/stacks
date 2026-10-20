/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme

/-!
# Deformation category of a scheme

Compatibility checks for residue objects and their deformation slices.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (FlatSchemeCat.ofResidue Λ k :
  ∀ (X : Scheme.{u}), (X ⟶ Spec (CommRingCat.of k)) → FlatSchemeCat Λ k)
#check (FlatSchemeCat.residueObj Λ k :
  ∀ (X : Scheme.{u}), (X ⟶ Spec (CommRingCat.of k)) →
    (FlatSchemeCat.forget Λ k).Fiber (ArtinianLocalAlgCat.residue Λ k))
#check (FlatSchemeCat.deformationCategory Λ k :
  ∀ (X : Scheme.{u}), (X ⟶ Spec (CommRingCat.of k)) → Type (u + 1))
