/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Resolution.Hom
import StacksCheckRecall

@[expose] public section

universe w v u

open CategoryTheory ComplexShape

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

section Projective

variable (P M N : CochainComplex C ℤ) (q : P ⟶ M)
variable [P.IsKProjective] [IsIso (DerivedCategory.Q.map q)]

/- Lemma 22.22.3 (1): a K-projective resolution computes morphisms out of its resolved object in
the derived category. -/
@[stacks 09KY]
#check
  (CochainComplex.Resolution.projectiveHomEquiv P M N q :
    ((HomotopyCategory.quotient C (up ℤ)).obj P ⟶
        (HomotopyCategory.quotient C (up ℤ)).obj N) ≃
      (DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj N))

end Projective

section Injective

variable (M N I : CochainComplex C ℤ) (i : N ⟶ I)
variable [I.IsKInjective] [IsIso (DerivedCategory.Q.map i)]

/- Lemma 22.22.3 (2): a K-injective resolution computes morphisms into its resolved object in the
derived category. -/
@[stacks 09KY]
#check
  (CochainComplex.Resolution.injectiveHomEquiv M N I i :
    ((HomotopyCategory.quotient C (up ℤ)).obj M ⟶
        (HomotopyCategory.quotient C (up ℤ)).obj I) ≃
      (DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj N))

end Injective

/- The reusable API also records the two comparison formulas explicitly. -/
#check @CochainComplex.Resolution.projectiveHomEquiv_apply
#check @CochainComplex.Resolution.injectiveHomEquiv_apply
