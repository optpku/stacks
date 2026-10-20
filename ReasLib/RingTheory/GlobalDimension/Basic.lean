/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Global Dimension of Rings

This module owns the ring-level formulation of a uniform bound on the projective
dimensions of modules. The ambient module-theoretic predicate remains
`HasProjectiveDimensionLE`; the declarations here package its uniform ring-level
counterparts.
-/

open CategoryTheory

universe u v

section

variable (R : Type u) [Ring R]

/-- A ring has global dimension at most `n` when every module over it has projective dimension
at most `n`. -/
@[stacks 00O6]
class HasGlobalDimensionLE (n : ℕ) : Prop where
  /-- Every `R`-module has projective dimension at most `n`. -/
  hasProjectiveDimensionLE (M : ModuleCat.{u} R) : HasProjectiveDimensionLE M n

/-- A ring has finite global dimension when there is a uniform finite bound on
the projective dimensions of all of its modules. -/
@[stacks 00O6]
class IsFiniteGlobalDimensionRing : Prop where
  /-- There is a finite uniform bound on the projective dimensions of all `R`-modules. -/
  exists_bound : ∃ n : ℕ, HasGlobalDimensionLE R n

namespace HasGlobalDimensionLE

/-- Every module over a ring of global dimension at most `n` has projective dimension at most
`n`. -/
@[stacks 00O6 "global-dimension bound in any module universe"]
theorem hasProjectiveDimensionLE_of_module
    {R : Type u} [Ring R] {M : ModuleCat.{v} R} {n : ℕ}
    [HasGlobalDimensionLE R n] :
    HasProjectiveDimensionLE M n := sorry

end HasGlobalDimensionLE

/-- Every module over a ring of global dimension at most `n` has projective dimension at most
`n`. -/
instance instHasProjectiveDimensionLE
    (n : ℕ) [HasGlobalDimensionLE R n] (M : ModuleCat.{v} R) :
    HasProjectiveDimensionLE M n :=
  HasGlobalDimensionLE.hasProjectiveDimensionLE_of_module (R := R) (M := M) (n := n)

/-- The least uniform projective-dimension bound of a ring of finite global
dimension. -/
@[stacks 00O6]
noncomputable def globalDimension [IsFiniteGlobalDimensionRing R] : ℕ :=
  sInf { n : ℕ | HasGlobalDimensionLE R n }

/-- The global dimension is itself an admissible uniform bound. -/
theorem hasGlobalDimensionLE_globalDimension [IsFiniteGlobalDimensionRing R] :
    HasGlobalDimensionLE R (globalDimension R) := sorry

/-- A ring of finite global dimension automatically carries its least
global-dimension bound as an instance. -/
noncomputable instance instHasGlobalDimensionLEGlobalDimension
    [IsFiniteGlobalDimensionRing R] :
    HasGlobalDimensionLE R (globalDimension R) :=
  hasGlobalDimensionLE_globalDimension R

/-- Every admissible uniform projective-dimension bound dominates the global
dimension. -/
theorem globalDimension_le {n : ℕ} [IsFiniteGlobalDimensionRing R]
    [HasGlobalDimensionLE R n] :
    globalDimension R ≤ n := sorry

end
