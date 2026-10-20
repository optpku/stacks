/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Prorepresentable
public import ReasLib.AlgebraicGeometry.FormalDeformation.GroupoidCompletion

/-!
# Prorepresentability and representability of completion

A groupoid in functors on Artinian local algebras is prorepresentable if and only if
its completion is representable as a groupoid in functors on complete local algebras.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- A groupoid in functors on Artinian local algebras is prorepresentable exactly when
its completion is representable as a groupoid in functors on complete local algebras. -/
theorem isProrepresentable_iff_isRepresentable_completion
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)) :
    IsProrepresentable G ↔ IsRepresentable (completion G) :=
  sorry

end CategoryTheory.GroupoidInFunctors
