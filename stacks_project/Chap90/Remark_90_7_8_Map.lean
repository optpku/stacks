/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompletionFunctoriality

/-!
# Stagewise action on formal objects

The stagewise functor and transformation actions are supplied by the shared completion owner.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X Y : BasedCategory.{v, v} (ArtinianLocalAlgCat Λ k)}

/- A based functor acts on formal objects by preserving bases and mapping every stage. -/
#check (FormalObject.map : (φ : X ⥤ᵇ Y) → FormalObject X.p ⥤ FormalObject Y.p)

/- A vertical transformation acts on formal objects through its stage components. -/
#check (FormalObject.map₂ : {φ ψ : X ⥤ᵇ Y} → (t : φ ⟶ ψ) →
  FormalObject.map φ ⟶ FormalObject.map ψ)
