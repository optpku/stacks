/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.IndEtale.Fiber

@[expose] public section

/-!
# Lemma 15.45.12 (0AH1)

@stack 0AH1
-/

-- Lemma 15.45.12 (1): a Noetherian filtered colimit of etale algebras has
-- only finitely many primes over a fixed base prime.
@[stacks 0AH1 "Lemma 15.45.12 (1)"]
#check @RingHom.IndEtale.primesOver_finite

-- Lemma 15.45.12 (2): its fiber is canonically the product of the residue
-- fields at those primes.
#check @Ideal.fiberToPiResidueField
@[stacks 0AH1 "Lemma 15.45.12 (2)"]
#check @RingHom.IndEtale.fiberToPiResidueField_bijective

-- Lemma 15.45.12 (3): the induced residue-field extensions are separable
-- algebraic extensions.
@[stacks 0AH1 "Lemma 15.45.12 (3)"]
#check @RingHom.IndEtale.residueField_isAlgebraic_and_separable

-- The fiber-Noetherian forms are the reusable companions behind parts (1)
-- and (2).
#check @RingHom.IndEtale.primesOver_finite_of_isNoetherianFiber
#check @RingHom.IndEtale.fiberToPiResidueField_bijective_of_isNoetherianFiber
