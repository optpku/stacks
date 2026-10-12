/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import ReasLib.CategoryTheory.Linear.Ideal.Nilpotent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived completeness of homotopy limits

@stack 091W

Derived completeness is closed under sequential homotopy limits.  Nilpotent ideal actions and
power-torsion systems are exposed as separate, reusable specializations of that closure principle.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.SequentialInverseSystem

variable {A : Type u} [CommSemiring A]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear A C]

/-- A sequential inverse system is power torsion with respect to `I` when `I` acts nilpotently on
every stage. -/
@[stacks 091W "power-torsion inverse system"]
def IsPowerTorsion (K : SequentialInverseSystem C) (I : Ideal A) : Prop :=
  ∀ n : ℕ, I.IsNilpotentOn (K.obj (Opposite.op n))

end CategoryTheory.SequentialInverseSystem

namespace Ideal.IsNilpotentOn

variable {A : Type u} [CommRing A]

/-- A nilpotent action of `I` on a derived `A`-module makes it derived complete with respect to
`I`. -/
@[stacks 091W "power-annihilated derived objects are derived complete"]
theorem isDerivedComplete {K : DerivedCategory (ModuleCat.{u, u} A)} {I : Ideal A}
    (hK : I.IsNilpotentOn K) :
    K.IsDerivedCompleteWithRespectTo I := sorry

end Ideal.IsNilpotentOn

namespace CategoryTheory.DerivedCategory

variable {A : Type u} [CommRing A]

/-- The elementwise power formula for a nilpotent ideal action implies derived completeness. -/
@[stacks 091W "power-annihilated derived objects are derived complete"]
theorem isDerivedComplete_of_pow_smul_id_eq_zero
    {K : DerivedCategory (ModuleCat.{u, u} A)} {I : Ideal A}
    (hpow : ∀ f ∈ I, ∃ e : ℕ, (f ^ e : A) • 𝟙 K = 0) :
    K.IsDerivedCompleteWithRespectTo I := sorry

end CategoryTheory.DerivedCategory

namespace CategoryTheory.HomotopyLimit

variable {A : Type u} [CommRing A]
variable {Ksys : SequentialInverseSystem (DerivedCategory (ModuleCat.{u, u} A))}
variable {K : DerivedCategory (ModuleCat.{u, u} A)} {I : Ideal A}

/-- A homotopy limit of derived-complete stages is derived complete with respect to the same
ideal. -/
@[stacks 091W "homotopy limits preserve derived completeness"]
theorem IsOf.isDerivedComplete (hK : IsOf Ksys K)
    (hstage : ∀ n : ℕ, (Ksys.obj (Opposite.op n)).IsDerivedCompleteWithRespectTo I) :
    K.IsDerivedCompleteWithRespectTo I := sorry

/-- A homotopy limit of a stagewise `I`-power-torsion tower is derived complete with respect to
`I`. -/
@[stacks 091W "derived completeness from stagewise power torsion"]
theorem IsOf.isDerivedComplete_of_powerTorsion (hK : IsOf Ksys K)
    (hpow : Ksys.IsPowerTorsion I) :
    K.IsDerivedCompleteWithRespectTo I := sorry

end CategoryTheory.HomotopyLimit
