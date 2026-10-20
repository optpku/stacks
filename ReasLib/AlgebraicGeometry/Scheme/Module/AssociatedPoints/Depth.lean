/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.RingTheory.Depth

/-!
# Depth and associated points of scheme modules

This file relates stalk depth and associated points to isomorphisms of scheme modules.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsQuasicoherent]

/-- A morphism from a coherent module to a quasi-coherent module on a locally Noetherian scheme
is an isomorphism if, at every point, its stalk map is an isomorphism or the source stalk has
depth at least two and the point is not associated to the target. -/
theorem isIso_of_stalkwise_or_depth
    (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X,
      IsIso (moduleStalkHom x φ) ∨
        ((2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (stalkModuleCat ℱ x) ∧
          x ∉ associatedPoints 𝒢)) :
    IsIso φ := sorry

end AlgebraicGeometry.Scheme.Modules
