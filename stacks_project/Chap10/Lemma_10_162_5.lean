/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.Nagata.FiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Quasi-Finite Nagata Algebras

@stack 032T

The source-facing quasi-finite specialization is owned by the reusable
finite-type Nagata API.
-/

-- Lemma 10.162.5, tag `032T`: a quasi-finite algebra over a Nagata ring is
-- Nagata.
@[stacks 032T]
#check @NagataRing.of_quasiFinite
