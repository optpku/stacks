/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.AdicCompletion

/-!
# Adic completion over Artinian local bases

The completion functor preserves the Artinian local base of every deformation.
-/

@[expose] public section

open CategoryTheory Functor
open scoped BasedFunctor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (FlatAlgebraCat.adicCompletionBasedFunctor Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P] [IsNoetherianRing P] (J : Ideal P),
    BasedCategory.ofFunctor (FlatAlgebraCat.deformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor (FlatAlgebraCat.deformationForget Λ k (AdicCompletion J P)))
