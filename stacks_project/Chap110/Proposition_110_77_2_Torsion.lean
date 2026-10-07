module

public import stacks_project.Chap110.Proposition_110_77_1_Torsion

/-!
# Torsion modules as a Serre class

The classical Serre class of torsion modules, obtained by specializing `S`-torsion to the
multiplicative set of non-zero-divisors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace ModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- The object property of torsion modules: the kernel of localization at the non-zero-divisors. -/
abbrev isTorsion : ObjectProperty (ModuleCat.{v} R) :=
  isTorsion' (nonZeroDivisors R)

/-- A bundled module is torsion iff it is torsion in the module-theoretic sense. -/
theorem isTorsion_iff (M : ModuleCat.{v} R) :
    isTorsion M ↔ Module.IsTorsion R M :=
  sorry

/-- A bundled module is torsion iff every element is annihilated by some non-zero-divisor. -/
theorem isTorsion_iff_exists_smul_eq_zero (M : ModuleCat.{v} R) :
    isTorsion M ↔ ∀ m : M, ∃ a : nonZeroDivisors R, (a : R) • m = 0 :=
  sorry

/-- The torsion modules form a Serre class, as the kernel of exact localization at the
non-zero-divisors. -/
instance instIsSerreClassIsTorsion :
    (isTorsion : ObjectProperty (ModuleCat.{v} R)).IsSerreClass :=
  inferInstance

end ModuleCat
