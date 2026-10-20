/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger

/-!
# Rim-Schlessinger implies Schlessinger's conditions

A functor satisfying the Rim-Schlessinger condition satisfies Schlessinger's
conditions (S1) and (S2).
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- A functor to Artinian local algebras satisfying the Rim-Schlessinger condition
satisfies Schlessinger's condition (S1). -/
@[stacks 06J7]
instance HasRimSchlessinger.toHasSchlessingerS1
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] :
    HasSchlessingerS1 p := sorry

/-- A functor to Artinian local algebras satisfying the Rim-Schlessinger condition
satisfies Schlessinger's condition (S2). -/
@[stacks 06J7]
instance HasRimSchlessinger.toHasSchlessingerS2
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] :
    HasSchlessingerS2 p := sorry

end CategoryTheory.Functor
