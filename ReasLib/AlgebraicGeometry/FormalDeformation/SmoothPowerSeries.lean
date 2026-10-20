/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.PowerSeries
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothFunctor

/-!
# Smoothness of restricted coyoneda maps

A morphism in `CompleteLocalAlgCat Λ k` induces a smooth map of restricted coyoneda
functors on `ArtinianLocalAlgCat` if and only if the target is a finite-variable
power series ring over the source.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- For a morphism `f : R ⟶ S` of complete local algebras, the induced morphism
`restrictedCoyoneda S ⟶ restrictedCoyoneda R` is smooth if and only if `S` is a
finite-variable power series ring over `R` along `f`. -/
@[stacks 06HL]
theorem restrictedCoyonedaMap_isSmooth_iff {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    NatTrans.IsSmooth (restrictedCoyonedaMap f) ↔ IsPowerSeriesOver f :=
  sorry

end CompleteLocalAlgCat
