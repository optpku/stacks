/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatScheme
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger

/-!
# Rim-Schlessinger condition for flat schemes

The projection from flat schemes over Artinian local algebras to their base
algebras satisfies the Rim-Schlessinger condition.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeCat

/-- The projection from flat schemes over Artinian local algebras to their base
algebras satisfies the Rim-Schlessinger condition. -/
instance instHasRimSchlessinger_forget : HasRimSchlessinger (forget Λ k) := sorry

end FlatSchemeCat
