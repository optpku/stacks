/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.Ext.ShortExact
public import ReasLib.CategoryTheory.Linear.IdealProjective.Ext

@[expose] public section

/-!
# Ideal-projectivity in short exact sequences

@stack 0G95

In a linear abelian category, the kernel term of a short exact sequence is ideal-projective when
the quotient term is ideal-projective and the middle term is projective.
-/

universe w t v u

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type t} [Ring R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C] [HasExt.{w} C]
variable {I : Ideal R} {S : ShortComplex C}

/-- Ideal-projectivity passes from the quotient term to the kernel term across a projective
middle term. -/
@[stacks 0G95 "ideal-projectivity of the kernel term"]
theorem idealProjective_X₁ (hS : S.ShortExact)
    (hX₃ : CategoryTheory.idealProjective I S.X₃) [Projective S.X₂] :
    CategoryTheory.idealProjective I S.X₁ := sorry

end CategoryTheory.ShortComplex.ShortExact
