module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety
public import stacks_project.Chap98.Remark_98_20_2_Strong_effectiveness
public import stacks_project.Chap100.Example_100_12_5_Quotient
public import stacks_project.Chap110.Lemma_110_73_1_RingSystem

/-!
# An algebraic stack not satisfying strong formal effectiveness

The classifying stack of an abelian variety over an algebraically closed field
that is not an algebraic closure of a finite field admits a sequential inverse
system of objects which is not effective in the sense of Remark 98.20.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.StrongEffectiveness
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.StrongEffectiveness

/-- Lemma 110.73.1: if `k` is algebraically closed and not an algebraic closure of a
finite field, and `A` is a nonzero abelian variety over `k` (`¬ IsIso A.hom`), then
the classifying stack `AlgebraicStack.classifying (Grp.mk A)` admits a `System` that
is not `System.IsEffective` in the sense of Remark 98.20.2. -/
@[stacks 0CXX]
theorem exists_not_isEffective {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ¬ ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : Algebra F k),
      IsAlgClosure F k)
    (A : SchemeOverField k) [GrpObj A] [AbelianVariety A] (hA : ¬ IsIso A.hom) :
    ∃ ξ : System (AlgebraicStack.classifying (Grp.mk A)), ¬ ξ.IsEffective := sorry

/-- There is a non-effective system on `AlgebraicStack.classifying (Grp.mk A)` whose
ring system is the triangle system `k[x, y] / I^{n+1}` with coefficient ring `k`. -/
theorem exists_not_isEffective_of_triangle {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ¬ ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : Algebra F k),
      IsAlgClosure F k)
    (A : SchemeOverField k) [GrpObj A] [AbelianVariety A] (hA : ¬ IsIso A.hom) :
    ∃ ξ : System (AlgebraicStack.classifying (Grp.mk A)),
      ξ.ringSystem = system k ∧ ξ.coeffRing = CommRingCat.of k ∧ ¬ ξ.IsEffective := sorry

end AlgebraicGeometry.GroupoidsOver.StrongEffectiveness
