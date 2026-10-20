/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_2_3_Trivial
public import ReasLib.RingTheory.RingHom.SquareZero.AlgebraExtension
public import stacks_project.Chap91.Lemma_91_2_2
import StacksCheckRecall

/-!
# Classification of square-zero A-algebra extensions of B by N

Isomorphism classes of extensions 0 ⟶ N ⟶ B' ⟶ B ⟶ 0 of A-algebras in which
N is an ideal of square zero are canonically bijective to Ext¹_B(NL_{B/A}, N).
-/

@[expose] public section

noncomputable section

universe u

open RingHom.SquareZeroExtension

/- Lemma 91.2.3 Let A be a ring. Let B be an A-algebra. Let N be a B-module.
The set of isomorphism classes of extensions of A-algebras
0 ⟶ N ⟶ B' ⟶ B ⟶ 0 where N is an ideal of square zero is canonically
bijective to Ext¹_B(NL_{B/A}, N). -/
@[stacks 0GPT] #check (RingHom.SquareZeroExtension.algebraExtensionEquiv :
  ∀ (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N],
    extOneNaiveCotangent A B N ≃
      RingHom.SquareZeroExtension.IsoClass (RingHom.id A) B
        (RingHom.SquareZeroExtension.zeroKernelMap A B N))
