/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Relative.BaseChange
import StacksCheckRecall

/-!
# Lemma 15.81.7

@stack 065C
-/

@[expose] public section

universe u v w x

/-! # Lemma 15.81.7: transitivity of relative finite presentation -/

/- Lemma 15.81.7, tag `065C`: relative finite presentation is transitive across a finitely
presented intermediate algebra. -/
@[stacks 065C "transitivity of relative finite presentation"]
#check fun {R : Type u} {A : Type v} {B : Type w} {M : Type x}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [AddCommGroup M] [Module B M] [Algebra.FinitePresentation R A]
    (hM : Module.FinitePresentationRelativeTo A B M) ↦
  (Module.FinitePresentationRelativeTo.trans hM :
    Module.FinitePresentationRelativeTo R B M)
