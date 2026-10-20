/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.Single
public import ReasLib.Algebra.Category.ModuleCat.DualNumber.Residue

@[expose] public section

/-!
# The periodic chain complex over the dual numbers

The `ℕ`-indexed chain complex here models the cohomological complex supported in nonpositive
degrees.  It reuses `HomologicalComplex.alternatingConst`, so parity, shape, and zero composites
are owned by the generic Mathlib construction.

@stack 0A5Q
@stack 0A5U
-/

noncomputable section

universe u

open CategoryTheory

namespace DualNumber.Periodic

variable (k : Type u) [CommRing k]

/-- The chain complex `⋯ ⟶ k[ε] ⟶ k[ε] ⟶ k[ε]` with every differential given by
multiplication by `ε`, ending in degree `0`. -/
@[stacks 0A5Q "the periodic dual-number projective complex",
  stacks 0A5U "the periodic dual-number injective complex"]
noncomputable def complex :
    ChainComplex (ModuleCat (DualNumber k)) ℕ :=
  HomologicalComplex.alternatingConst
    (ModuleCat.of (DualNumber k) (DualNumber k))
    (φ := epsEnd k) (ψ := epsEnd k)
    (epsEnd_sq k) (epsEnd_sq k)
    (fun _ _ h ↦ ComplexShape.down_nat_odd_add h)

/-- Every term of the periodic complex is the regular dual-number module. -/
theorem complex_X (n : ℕ) :
    (complex k).X n = ModuleCat.of (DualNumber k) (DualNumber k) := sorry

/-- Every nonzero differential of the periodic complex is multiplication by `ε`. -/
theorem complex_d (n : ℕ) :
    (complex k).d (n + 1) n = epsEnd k := sorry

/-- The residue quotient annihilates the differential entering degree `0`. -/
theorem augmentationCondition :
    (complex k).d 1 0 ≫ residueQuotient k = 0 := sorry

/-- The canonical augmentation of the periodic complex to the residue module in degree `0`. -/
@[stacks 0A5Q "the periodic dual-number augmentation",
  stacks 0A5U "the periodic dual-number augmentation"]
noncomputable def augmentation :
    complex k ⟶
      (ChainComplex.single₀ (ModuleCat (DualNumber k))).obj (residueModule k) :=
  (ChainComplex.toSingle₀Equiv (complex k) (residueModule k)).symm
    ⟨residueQuotient k, augmentationCondition k⟩

/-- The degree-zero component of the periodic augmentation is the residue quotient. -/
theorem augmentation_f_zero :
    (augmentation k).f 0 = residueQuotient k := sorry

/-- The periodic augmentation is a quasi-isomorphism. -/
@[stacks 0A5Q "the periodic dual-number projective resolution",
  stacks 0A5U "the periodic dual-number injective resolution"]
instance augmentationQuasiIso : QuasiIso (augmentation k) := sorry

end DualNumber.Periodic
