/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.Exact
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory.ShortComplex

open FilteredObject FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (FilteredObject C)}
variable (h₁ : S.X₁.IsFinite) (h₂ : S.X₂.IsFinite) (h₃ : S.X₃.IsFinite)
variable (hgr : (S.map associatedGradedFunctor).Exact)

/- Lemma 12.19.15 [05QH] (1): associated-graded exactness is exact in every degree. -/
@[stacks 05QH]
#check (Filtered.AssociatedGraded.exact_piece (S := S) hgr :
  ∀ p : ℤ, (S.map (associatedGradedFunctor ⋙ GradedObject.eval p)).Exact)

/- Lemma 12.19.15 [05QH] (2): associated-graded exactness of finite filtrations implies exactness
on every filtration stage. -/
@[stacks 05QH]
#check (Filtered.AssociatedGraded.exact_stage (S := S) h₁ h₂ h₃ hgr :
  ∀ p : ℤ, (S.map (FilteredObject.Stage.functor p)).Exact)

/- Lemma 12.19.15 [05QH] (3): associated-graded exactness of finite filtrations implies exactness
on every quotient by a filtration stage. -/
@[stacks 05QH]
#check (Filtered.AssociatedGraded.exact_quotient (S := S) h₁ h₂ h₃ hgr :
  ∀ p : ℤ, (S.map (quotientFunctor p)).Exact)

/- Lemma 12.19.15 [05QH] (4a): associated-graded exactness makes the first map strict. -/
@[stacks 05QH]
#check (Filtered.AssociatedGraded.strict_f (S := S) h₁ h₂ h₃ hgr : Strict S.f)

/- Lemma 12.19.15 [05QH] (4b): associated-graded exactness makes the second map strict. -/
@[stacks 05QH]
#check (Filtered.AssociatedGraded.strict_g (S := S) h₁ h₂ h₃ hgr : Strict S.g)

/- Lemma 12.19.15 [05QH] (5): the underlying short complex is exact. -/
@[stacks 05QH]
#check (Filtered.AssociatedGraded.exact_underlying (S := S) h₁ h₂ h₃ hgr :
  (S.map FilteredObject.forget).Exact)

end CategoryTheory.ShortComplex
