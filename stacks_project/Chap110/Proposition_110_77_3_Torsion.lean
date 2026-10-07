module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import stacks_project.Chap110.Proposition_110_77_2_Torsion

/-!
# Finitely generated torsion modules as a Serre class

The Serre class of finitely generated torsion modules, obtained by pulling back
`ModuleCat.isTorsion` along `forget₂` from `FGModuleCat` to `ModuleCat`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace FGModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- The object property of finitely generated torsion modules: the inverse image of
`ModuleCat.isTorsion` along `forget₂`. -/
abbrev isTorsion : ObjectProperty (FGModuleCat.{v} R) :=
  ModuleCat.isTorsion.inverseImage
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R))

/-- A finitely generated module is torsion iff it is torsion in the module-theoretic sense. -/
theorem isTorsion_iff (M : FGModuleCat.{v} R) :
    isTorsion M ↔ Module.IsTorsion R M :=
  sorry

/-- A finitely generated module is torsion iff every element is annihilated by some
non-zero-divisor. -/
theorem isTorsion_iff_exists_smul_eq_zero (M : FGModuleCat.{v} R) :
    isTorsion M ↔ ∀ m : M, ∃ a : nonZeroDivisors R, (a : R) • m = 0 :=
  sorry

/-- The finitely generated torsion modules form a Serre class, as the inverse image of a
Serre class along the exact forgetful functor from `FGModuleCat`. -/
instance instIsSerreClassIsTorsion [IsNoetherianRing R] :
    (isTorsion : ObjectProperty (FGModuleCat.{v} R)).IsSerreClass :=
  inferInstance

end FGModuleCat
