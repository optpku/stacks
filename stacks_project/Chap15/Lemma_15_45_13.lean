/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Henselian.Henselization.Fiber

@[expose] public section

/-!
# Lemma 15.45.13 (07QQ)

@stack 07QQ
-/

-- Lemma 15.45.13 (1): finiteness of the primes of a henselization
-- over a fixed base prime.
@[stacks 07QQ "Lemma 15.45.13 (1)"]
#check @IsHenselizationOf.primesOver_finite

-- Lemma 15.45.13 (2): the canonical product decomposition of the
-- henselization fiber.
@[stacks 07QQ "Lemma 15.45.13 (2)"]
#check @IsHenselizationOf.fiberToPiResidueField_bijective

-- Lemma 15.45.13 (3): finiteness of the primes of a strict
-- henselization over a fixed base prime.
@[stacks 07QQ "Lemma 15.45.13 (3)"]
#check @IsStrictHenselizationOf.primesOver_finite

-- Lemma 15.45.13 (4): the canonical product decomposition of the
-- strict-henselization fiber.
@[stacks 07QQ "Lemma 15.45.13 (4)"]
#check @IsStrictHenselizationOf.fiberToPiResidueField_bijective

-- Lemma 15.45.13 (5): the henselization residue-field extensions are
-- separable algebraic.
@[stacks 07QQ "Lemma 15.45.13 (5)"]
#check @IsHenselizationOf.residueField_isAlgebraic_and_separable

-- Lemma 15.45.13 (6): the strict-henselization residue-field
-- extensions are separable algebraic.
@[stacks 07QQ "Lemma 15.45.13 (6)"]
#check @IsStrictHenselizationOf.residueField_isAlgebraic_and_separable
