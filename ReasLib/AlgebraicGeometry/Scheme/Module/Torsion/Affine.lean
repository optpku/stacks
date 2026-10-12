/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion

/-!
# Torsion-free modules on affine opens

Torsion-freeness of quasicoherent module sheaves on integral schemes can be detected on the
modules of sections over affine opens.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

/-- A quasicoherent module sheaf on an integral scheme is torsion free exactly when its module
of sections on every affine open is torsion free over the corresponding ring of functions. -/
theorem isTorsionFree_iff_affineOpen
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsTorsionFree ℱ ↔
      ∀ U : X.Opens, IsAffineOpen U → Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U)) := sorry

/-- Affine-open sections of a torsion-free quasicoherent module sheaf on an integral scheme are
torsion free over the corresponding ring of functions. -/
theorem IsTorsionFree.torsionFree_sections
    {ℱ : X.Modules} [ℱ.IsQuasicoherent] (hℱ : IsTorsionFree ℱ)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U)) :=
  (isTorsionFree_iff_affineOpen ℱ).1 hℱ U hU

/-- A quasicoherent module sheaf on an integral scheme is torsion free exactly when its module
of sections on every bundled affine open is torsion free over the corresponding ring of
functions. -/
theorem isTorsionFree_iff_affineOpens
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsTorsionFree ℱ ↔
      ∀ U : X.affineOpens, Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U)) := by
  constructor
  · intro hℱ U
    exact hℱ.torsionFree_sections U.1 U.2
  · intro hℱ
    exact (isTorsionFree_iff_affineOpen ℱ).2 fun U hU ↦ by
      simpa using hℱ ⟨U, hU⟩

/-- Sections of a torsion-free quasicoherent module sheaf on a bundled affine open of an
integral scheme are torsion free over the corresponding ring of functions. -/
theorem IsTorsionFree.torsionFree_sections_affineOpen
    {ℱ : X.Modules} [ℱ.IsQuasicoherent] (hℱ : IsTorsionFree ℱ) (U : X.affineOpens) :
    Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U)) := by
  simpa using hℱ.torsionFree_sections U.1 U.2

/-- A quasicoherent module sheaf on an integral scheme is torsion free if its sections on every
affine open are torsion free over the corresponding ring of functions. -/
theorem isTorsionFree_of_affineOpen
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (hℱ : ∀ U : X.Opens, IsAffineOpen U → Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U))) :
    IsTorsionFree ℱ :=
  (isTorsionFree_iff_affineOpen ℱ).2 hℱ

/-- A quasicoherent module sheaf on an integral scheme is torsion free if its sections on every
bundled affine open are torsion free over the corresponding ring of functions. -/
theorem isTorsionFree_of_affineOpens
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (hℱ : ∀ U : X.affineOpens, Module.IsTorsionFree (Γ(X, U)) (Γ(ℱ, U))) :
    IsTorsionFree ℱ :=
  (isTorsionFree_iff_affineOpens ℱ).2 hℱ

end AlgebraicGeometry.Scheme.Modules
