/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ChainComplex.Exact
public import ReasLib.Algebra.Homology.HomologicalComplex.Biproduct

/-!
# Exactness of binary biproduct chain complexes

This leaf owns the degreewise exactness consequences of the pointwise binary biproduct
construction.  It is independent of finite-free coordinates and of local-ring hypotheses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

namespace HomologicalComplex.ExactAt

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]

/-- Exactness of a binary biproduct chain complex descends to its first summand. -/
@[stacks 00N1 "exactness descends to the first biproduct summand"]
theorem of_biprod_fst
    {K L : ChainComplex C ℕ} {j : ℕ}
    (h : (biprod K L).ExactAt j) :
    K.ExactAt j := sorry

/-- Exactness of a binary biproduct chain complex descends to its second summand. -/
@[stacks 00N1 "exactness descends to the second biproduct summand"]
theorem of_biprod_snd
    {K L : ChainComplex C ℕ} {j : ℕ}
    (h : (biprod K L).ExactAt j) :
    L.ExactAt j := sorry

end HomologicalComplex.ExactAt
