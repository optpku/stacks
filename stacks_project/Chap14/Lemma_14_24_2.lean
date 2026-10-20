/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Equivalence.IsEquivalence.OfFaithful
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksCheckRecall

/-!
@stack 019F

# Lemma 14.24.2 compatibility facade

The source hypotheses remain visible here.  ReasLib separately owns the assumption-minimal
categorical construction and its explicit quasi-inverse data.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe vA uA vB uB

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable (F : A ⥤ B) (G : B ⥤ A) [F.Faithful] [G.EssSurj]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [PreservesFiniteLimits G] [PreservesFiniteColimits G]
variable (counitIso : G ⋙ F ≅ 𝟭 B)

/- Lemma 14.24.2: the resulting equivalence retains the specified forward and inverse functors. -/
@[stacks 019F "Lemma 14.24.2"]
#check (Functor.IsEquivalence.ofFaithful.equivalence F G counitIso : A ≌ B)

#check (Functor.IsEquivalence.ofFaithful.quasiInverse F G counitIso :
  Functor.QuasiInverse F)

#check (Functor.IsEquivalence.ofFaithful.comparison.iso.app F G counitIso :
  ∀ X : A,
    (Functor.IsEquivalence.ofFaithful.comparison.iso F G counitIso).app X =
      Functor.IsEquivalence.ofFaithful.comparison.app F G counitIso X)

@[stacks 019F "Lemma 14.24.2, specified forward functor"]
#check (Functor.IsEquivalence.ofFaithful.equivalence.functor F G counitIso :
  (Functor.IsEquivalence.ofFaithful.equivalence F G counitIso).functor = F)

@[stacks 019F "Lemma 14.24.2, specified inverse functor"]
#check (Functor.IsEquivalence.ofFaithful.equivalence.inverse F G counitIso :
  (Functor.IsEquivalence.ofFaithful.equivalence F G counitIso).inverse = G)

#check (Functor.IsEquivalence.ofFaithful.essSurj F G counitIso : F.IsEquivalence)
#check (Functor.IsEquivalence.ofFaithful.inverse F G counitIso : G.IsEquivalence)

end CategoryTheory
