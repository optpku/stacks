/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Relative.BaseChange
import StacksCheckRecall

/-!
# Lemma 15.81.6

@stack 0670
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

/-! # Lemma 15.81.6: base change of relative finite presentation -/

/- Lemma 15.81.6, tag `0670`: finitely presented extension of scalars preserves relative finite
presentation. -/
@[stacks 0670 "base change of relative finite presentation"]
#check fun {R : Type u} {A : Type v} {A' : Type w} {M : Type x}
    [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
    [AddCommGroup M] [Module A M] [Algebra.FinitePresentation A A']
    (hM : Module.FinitePresentationRelativeTo R A M) ↦
  (Module.FinitePresentationRelativeTo.baseChange hM :
    Module.FinitePresentationRelativeTo R A' (A' ⊗[A] M))
