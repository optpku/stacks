module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Length.Projective
import StacksCheckRecall

/-!
# Lemma 10.55.9
@stack 00JK
-/

@[expose] public section

/- Lemma 10.55.9 (Tag 00JK): the comparison `K₀(R) → K'_0(R)` intertwines projective rank
and finite-module length, with multiplication by `length_R(R)` on `ℤ`.  The map identity is the
primary reusable comparison-square API and remains polymorphic in the module universe. -/
@[stacks 00JK]
#check @CategoryTheory.ModuleCat.K0.finiteLength_comp_projectiveToFinite

/- The pointwise form is exposed for direct rewriting without evaluating a homomorphism equality
manually. -/
@[stacks 00JK]
#check @CategoryTheory.ModuleCat.K0.finiteLength_projectiveToFinite
