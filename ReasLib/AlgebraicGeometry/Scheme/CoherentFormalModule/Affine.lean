/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Sequential.FGModuleCat
public import Mathlib.RingTheory.AdicCompletion.Algebra

@[expose] public section

open CategoryTheory Opposite

universe u

namespace CategoryTheory.SequentialInverseSystem

variable {A : Type u} [CommRing A]

/-- A sequential inverse system of finite `A`-modules is an affine coherent formal module system
along `I` if its stage `n` is annihilated by `I ^ n` and its successor map induces a bijection
from the quotient of stage `n + 1` by `I ^ n` onto stage `n`. -/
def IsAffineCoherentFormalModuleSystem (I : Ideal A) :
    ObjectProperty (SequentialInverseSystem (FGModuleCat A)) :=
  fun F ↦
    (∀ n : ℕ,
      I ^ n • (⊤ : Submodule A (F.stageModule n)) = ⊥) ∧
    ∀ n : ℕ,
      ∃ hquot :
          I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))) ≤ (F.stepLinearMap n).ker,
        Function.Bijective
          (Submodule.liftQ
            (I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))))
            (F.stepLinearMap n)
            hquot)

/-- The full category of affine coherent formal module systems along an ideal `I` of `A`. -/
abbrev AffineCoherentFormalModules (A : Type u) [CommRing A] (I : Ideal A) :=
  (IsAffineCoherentFormalModuleSystem I).FullSubcategory

/-- A finite-module inverse system is an affine coherent formal module system exactly when its
stages are annihilated by the corresponding powers of `I` and its induced successor quotient maps
are bijective. -/
theorem isAffineCoherentFormalModuleSystem_iff {I : Ideal A}
    (F : SequentialInverseSystem (FGModuleCat A)) :
    IsAffineCoherentFormalModuleSystem I F ↔
      (∀ n : ℕ,
        I ^ n • (⊤ : Submodule A (F.stageModule n)) = ⊥) ∧
      ∀ n : ℕ,
        ∃ hquot :
            I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))) ≤ (F.stepLinearMap n).ker,
          Function.Bijective
            (Submodule.liftQ
              (I ^ n • (⊤ : Submodule A (F.stageModule (n + 1))))
              (F.stepLinearMap n)
              hquot) := sorry

namespace AffineCoherentFormalModules

variable [IsNoetherianRing A]

/-- The category of affine coherent formal module systems along `I` is equivalent to the category
of finite modules over the `I`-adic completion of `A`. -/
theorem nonemptyEquivalence (I : Ideal A) :
    Nonempty (AffineCoherentFormalModules A I ≌ FGModuleCat (AdicCompletion I A)) := sorry

end AffineCoherentFormalModules

end CategoryTheory.SequentialInverseSystem
