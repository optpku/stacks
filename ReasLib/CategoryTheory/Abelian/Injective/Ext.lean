/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.Injective.Characterizations
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.Data.List.TFAE

/-!
# Injectivity and Ext

@stack 0136
-/

@[expose] public section

open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Tag 0136: an object is injective exactly when every degree-one extension into it vanishes.
This is the zero-element formulation of Mathlib's
`injective_iff_subsingleton_ext_one`. -/
@[stacks 0136, stacks 0AVE]
theorem injective_iff_ext_one_eq_zero (I : C) :
    Injective I ↔ ∀ ⦃B : C⦄ (e : Ext B I 1), e = 0 := sorry

/-- Tag 0136: injectivity, exactness of the represented preadditive functor, splitting of short
exact sequences beginning at the object, and vanishing of `Ext¹(-, I)` are equivalent. -/
@[stacks 0136, stacks 0AVE]
theorem injective_tfae (I : C) :
    List.TFAE [
      Injective I,
      exactFunctor _ _ (preadditiveYonedaObj I),
      ∀ ⦃S : ShortComplex C⦄, S.X₁ = I → S.ShortExact → IsSplitMono S.f,
      ∀ ⦃B : C⦄ (e : Ext B I 1), e = 0
    ] := sorry

end CategoryTheory
