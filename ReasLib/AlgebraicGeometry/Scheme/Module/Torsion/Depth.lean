/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Reflexive
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Affine

/-!
# Depth criteria for torsion-free scheme modules

This file relates stalk depth to isomorphisms whose target is a torsion-free scheme module.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsQuasicoherent] [IsTorsionFree 𝒢]

/-- A morphism from a coherent module to a quasi-coherent torsion-free module on an integral
locally Noetherian scheme is an isomorphism if, at every point, its stalk map is an isomorphism
or the source stalk has depth at least two. -/
theorem isIso_of_stalkwise_or_depth_of_isTorsionFree
    (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X,
      IsIso (moduleStalkHom x φ) ∨
        (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (stalkModuleCat ℱ x)) :
    IsIso φ := sorry

end AlgebraicGeometry.Scheme.Modules
