/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.Injective.Ext
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Abelian.Ext CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (I : C)

/- Lemma 12.27.2 (1) ↔ (2) [0136]: injectivity is detected by exactness of the preadditive
Yoneda functor. -/
@[stacks 0136]
#check (injective_iff_exact_preadditiveYonedaObj I :
  Injective I ↔ exactFunctor _ _ (preadditiveYonedaObj I))

/- Lemma 12.27.2 (1) ↔ (3) [0136]: injectivity is detected by splitting every short exact
sequence beginning at the object. -/
@[stacks 0136]
#check (injective_iff_shortExact_isSplitMono I :
  Injective I ↔
    ∀ ⦃S : ShortComplex C⦄, S.X₁ = I → S.ShortExact → IsSplitMono S.f)

section

variable [HasExt.{w} C]

/- Lemma 12.27.2 (1) ↔ (4) [0136]: injectivity is detected by vanishing of all degree-one
extensions into the object. -/
@[stacks 0136]
#check (injective_iff_ext_one_eq_zero I :
  Injective I ↔ ∀ ⦃B : C⦄ (e : Ext B I 1), e = 0)

/- Lemma 12.27.2 [0136]: the source's four equivalent characterizations. -/
@[stacks 0136]
#check (injective_tfae I :
  List.TFAE [
    Injective I,
    exactFunctor _ _ (preadditiveYonedaObj I),
    ∀ ⦃S : ShortComplex C⦄, S.X₁ = I → S.ShortExact → IsSplitMono S.f,
    ∀ ⦃B : C⦄ (e : Ext B I 1), e = 0])

end
