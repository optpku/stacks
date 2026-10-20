/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Hypersurface
import StacksCheckRecall

@[expose] public section

universe u

open IsLocalRing

/- Remark 111.28.9: a complete Noetherian local Cohen-Macaulay ring of Krull dimension 1
and embedding dimension 2 is of the form `B ⧸ Ideal.span {F}`, where `B` is a 2-dimensional
regular local ring. Completeness is a sufficient niceness hypothesis for this presentation. -/
@[stacks 02EN] #check
  (IsLocalRing.exists_dimTwo_regular_spanSingleton_quotient :
    ∀ {A : Type u} [CommRing A] [IsCompleteLocalRing A] [IsNoetherianRing A]
      [Module.CohenMacaulay A A],
      ringKrullDim A = 1 →
        Module.finrank (ResidueField A) (CotangentSpace A) = 2 →
          ∃ (B : Type u) (_ : CommRing B) (_ : IsRegularLocalRing B) (F : B),
            ringKrullDim B = 2 ∧ Nonempty ((B ⧸ Ideal.span {F}) ≃+* A))
