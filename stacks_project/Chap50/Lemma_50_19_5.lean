/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap50.Lemma_50_19_5_FrobeniusTrace
import StacksCheckRecall

/- Lemma 50.19.5 (1): the relative Frobenius of a smooth morphism of fixed relative
dimension in prime characteristic is finite. -/
@[stacks 0FW2] #check AlgebraicGeometry.Scheme.Hom.relativeFrobenius_isFinite_of_smooth

/- Lemma 50.19.5 (2): the relative Frobenius of a smooth morphism of fixed relative
dimension in prime characteristic is syntomic. -/
@[stacks 0FW2] #check AlgebraicGeometry.Scheme.Hom.relativeFrobenius_syntomic_of_smooth

/- Lemma 50.19.5 (3): the relative de Rham trace of the relative Frobenius vanishes in
every degree different from the relative dimension. -/
@[stacks 0FW2] #check
  AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.relativeFrobeniusTrace_eq_zero

/- Lemma 50.19.5 (4): the relative de Rham trace of the relative Frobenius is an
epimorphism in the relative dimension. -/
@[stacks 0FW2] #check
  AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.relativeFrobeniusTrace_epi
