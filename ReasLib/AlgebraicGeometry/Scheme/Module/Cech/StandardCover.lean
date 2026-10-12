/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech
public import ReasLib.AlgebraicGeometry.Scheme.StandardZariskiCover.AffineOpen

/-!
# Čech cohomology on standard covers

This module records the positive-degree Čech acyclicity of quasi-coherent
modules on standard distinguished-open covers of affine opens.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.StandardZariskiCover.OnAffineOpen

variable {X : Scheme.{u}} {U : X.affineOpens}

/-- A quasi-coherent module is Čech-acyclic on a standard distinguished-open
cover of an affine open. -/
theorem isCechAcyclicFamily
    (𝒰 : StandardZariskiCover.OnAffineOpen.{u, u} X U)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ∀ p : ℕ, 0 < p →
      CategoryTheory.Limits.IsZero
        (RingedSpace.moduleCechCohomology 𝒰.opens ℱ p) := sorry

end AlgebraicGeometry.Scheme.StandardZariskiCover.OnAffineOpen
