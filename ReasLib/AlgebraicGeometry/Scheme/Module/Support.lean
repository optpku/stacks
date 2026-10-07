module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberRank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration

/-!
# Supports of module sheaves on schemes

This file develops the support of module sheaves on schemes, including closedness for finite-type
modules, detection by residue-field fibers, behavior under pullback, and the affine comparison
with support of sections.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The support of a scheme module is the set of points where its stalk is nonzero. -/
abbrev moduleSupport (ℱ : X.Modules) : Set X :=
  RingedSpace.moduleSupport ℱ

variable (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/-- On an affine open, a prime supports the module of sections of a quasi-coherent module sheaf
exactly when its corresponding point supports the sheaf. -/
theorem mem_support_sections_iff_fromSpec_mem_support
    {U : X.Opens} (hU : IsAffineOpen U) (p : PrimeSpectrum (Γ(X, U))) :
    p ∈ Module.support (Γ(X, U)) (Γ(ℱ, U)) ↔
      hU.fromSpec p ∈ AlgebraicGeometry.RingedSpace.moduleSupport ℱ := sorry

/-- The support of a quasi-coherent module sheaf on a scheme is stable under specialization. -/
theorem stableUnderSpecialization_moduleSupport :
    StableUnderSpecialization (AlgebraicGeometry.RingedSpace.moduleSupport ℱ) := sorry

/-- The support of a finite-type module sheaf on a scheme is closed. -/
theorem isClosed_moduleSupport (ℱ : X.Modules) [ℱ.IsFiniteType] :
    IsClosed (moduleSupport ℱ) := sorry

/-- A finite-type module sheaf is supported at a point exactly when its residue-field fiber there
is nontrivial. -/
theorem mem_moduleSupport_iff_nontrivial_fiber
    (ℱ : X.Modules) [ℱ.IsFiniteType] (x : X) :
    x ∈ moduleSupport ℱ ↔ Nontrivial (fiber ℱ x) := sorry

/-- Pullback carries the support of a finite-type module sheaf to its inverse image. -/
theorem moduleSupport_pullback_eq_preimage
    {Y : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsFiniteType] (f : Y ⟶ X) :
    moduleSupport ((Scheme.Modules.pullback f).obj ℱ) =
      f.base ⁻¹' moduleSupport ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
