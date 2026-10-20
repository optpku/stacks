/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Ext.IntoField
import StacksCheckRecall

@[expose] public section

universe u

variable {A k : Type u} [CommRing A] [Field k]

/- Lemma 98.23.1: For a ring map `σ : A →+* k` to a field and a bounded-above
 derived `A`-module `E`, the canonical comparison identifies `Ext^i_A(E, k)`
 with `Hom_k(H^{-i}(E ⊗^L k), k)` in every integer degree. -/
@[stacks 07YK] #check
  (CategoryTheory.DerivedCategory.Ext.extToHomologyDual_bijective :
    ∀ (σ : A →+* k) (E : DerivedCategory.Minus (ModuleCat.{u} A))
      (i : ℤ), Function.Bijective
        (CategoryTheory.DerivedCategory.Ext.extToHomologyDual σ E i))
