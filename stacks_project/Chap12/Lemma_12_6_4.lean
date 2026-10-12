/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import StacksCheckRecall

@[expose] public section

universe w v u

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {S : ShortComplex C} (hS : S.ShortExact) (N : C)

/- Lemma 12.6.4 [05E2] (1): the contravariant six-term sequence is
the degree-zero/degree-one segment of the canonical long exact Ext sequence. -/
@[stacks 05E2]
#check (contravariantSequence_exact hS N 0 1 rfl :
  (contravariantSequence hS N 0 1 rfl).Exact)

#check (mono_precomp_mk₀_of_epi N S.g (hg := hS.epi_g))
#check (addEquiv₀ : Ext S.X₃ N 0 ≃+ (S.X₃ ⟶ N))

/- Lemma 12.6.4 [05E2] (2): the covariant six-term sequence is
the degree-zero/degree-one segment of the canonical long exact Ext sequence. -/
@[stacks 05E2]
#check (covariantSequence_exact N hS 0 1 rfl :
  (covariantSequence N hS 0 1 rfl).Exact)

#check (mono_postcomp_mk₀_of_mono N S.f (hf := hS.mono_f))
#check (addEquiv₀ : Ext N S.X₁ 0 ≃+ (N ⟶ S.X₁))

end CategoryTheory.Abelian.Ext
