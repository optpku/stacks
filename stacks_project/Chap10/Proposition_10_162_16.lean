/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Completion.Nagata
public import ReasLib.RingTheory.Normal.Nagata.Dedekind
public import ReasLib.RingTheory.Normal.Nagata.Field
public import ReasLib.RingTheory.Normal.Nagata.FiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Nagata Ring Examples and Finite-Type Stability

@stack 0335

The neutral examples and permanence theorem of this proposition are owned by
ReasLib.  This source file keeps the textbook grouping as a recall block.
-/

-- Proposition 10.162.16, tag `0335`: fields, Noetherian complete local rings,
-- and characteristic-zero Dedekind domains are Nagata; finite-type algebras
-- over Nagata rings are Nagata.
@[stacks 0335]
#check @NagataRing.instOfField
#check @IsCompleteLocalRing.nagataRing
#check @NagataRing.instOfDedekindDomainCharZero
#check @NagataRing.of_finiteType
#check (inferInstance : NagataRing ℤ)
