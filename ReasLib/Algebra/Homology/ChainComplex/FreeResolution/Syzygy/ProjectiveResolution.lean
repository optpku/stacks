/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.ProjectiveResolution.Syzygy
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution.Syzygy

/-!
# Free-resolution syzygies and projective resolutions

@stack 00NG
@stack 0CXC

This leaf connects the explicit module-kernel syzygies of an augmented free resolution to the
canonical categorical syzygies of its associated projective resolution. The raw syzygy tower remains
available without a freeness hypothesis; this bridge is intentionally isolated behind that extra
hypothesis.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ChainComplex.IsFreeResolution

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {F : ChainComplex (ModuleCat R) ℕ}

/-- The explicit syzygy family of a free resolution is definitionally the concrete kernel family
of its associated projective resolution. -/
@[simp, stacks 00NG "free-resolution syzygy kernel model"]
theorem syzygy_toProjectiveResolution
    (π : F ⟶ ChainComplex.moduleSingle R M) [IsFreeResolution π] (d : ℕ) :
    ChainComplex.syzygy π d =
      CategoryTheory.ModuleCat.ProjectiveResolution.kernelSyzygy
        (toProjectiveResolution π) d := sorry

/-- The explicit syzygy of a free resolution is canonically isomorphic to the categorical syzygy
of its associated projective resolution. -/
@[stacks 00NG "free-resolution categorical syzygy bridge"]
noncomputable def syzygyIso
    (π : F ⟶ ChainComplex.moduleSingle R M) [IsFreeResolution π] (d : ℕ) :
    ChainComplex.syzygy π d ≅ (toProjectiveResolution π).syzygy d :=
  (CategoryTheory.ModuleCat.ProjectiveResolution.kernelSyzygy.syzygyIsoKernel
    (toProjectiveResolution π) d).symm

end ChainComplex.IsFreeResolution
