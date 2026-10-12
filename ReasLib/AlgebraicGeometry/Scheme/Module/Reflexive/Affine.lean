/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Dual.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive

/-!
# Reflexive modules on affine opens

Reflexivity of coherent module sheaves on integral locally Noetherian schemes can be detected on
the modules of sections over affine opens.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
variable [AlgebraicGeometry.IsLocallyNoetherian X]

/-- A coherent module sheaf on an integral locally Noetherian scheme is reflexive exactly when
its module of sections on every affine open is reflexive. -/
theorem isReflexive_iff_affineOpen
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    IsReflexive ℱ ↔
      ∀ U : X.Opens, IsAffineOpen U → Module.IsReflexive (Γ(X, U)) (Γ(ℱ, U)) := sorry

namespace IsReflexive

/-- Sections of a reflexive coherent module sheaf on an affine open are reflexive over the
corresponding ring of functions. -/
theorem reflexive_sections
    (ℱ : X.Modules) [ℱ.IsCoherent] [IsReflexive ℱ] (U : X.Opens) (hU : IsAffineOpen U) :
    Module.IsReflexive (Γ(X, U)) (Γ(ℱ, U)) := sorry

/-- Sections of a reflexive coherent module sheaf on a bundled affine open are reflexive over the
corresponding ring of functions. -/
theorem reflexive_sections_affineOpen
    (ℱ : X.Modules) [ℱ.IsCoherent] [IsReflexive ℱ] (U : X.affineOpens) :
    Module.IsReflexive (Γ(X, U)) (Γ(ℱ, U)) :=
  reflexive_sections ℱ U.1 U.2

end IsReflexive

/-- A coherent module sheaf on an integral locally Noetherian scheme is reflexive exactly when
its module of sections on every bundled affine open is reflexive. -/
theorem isReflexive_iff_affineOpens
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    IsReflexive ℱ ↔
      ∀ U : X.affineOpens, Module.IsReflexive (Γ(X, U)) (Γ(ℱ, U)) := by
  constructor
  · intro hℱ U
    exact (isReflexive_iff_affineOpen ℱ).1 hℱ U.1 U.2
  · intro hℱ
    exact (isReflexive_iff_affineOpen ℱ).2 fun U hU ↦ by
      simpa using hℱ ⟨U, hU⟩

end AlgebraicGeometry.Scheme.Modules
