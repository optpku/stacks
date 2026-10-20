/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RegularLocalRing.Flat
import StacksCheckRecall

/-!
# Regularity Descent Along Flat Local Maps

The reusable regular-local descent theorem is owned by ReasLib. This source
file retains the Stacks-facing recall entry.

@stack 00OF
-/

@[expose] public section

/- Lemma 10.110.9 (Stacks tag `00OF`): if `R → S` is a flat local homomorphism of local
Noetherian rings and `S` is regular local, then `R` is regular local. -/
@[stacks 00OF]
#check @IsRegularLocalRing.of_flat_localHom_of_regularTarget

/- The map-first owner underlying the algebra-map specialization. -/
@[stacks 00OF "map-first regularity descent"]
#check @RingHom.Flat.isRegularLocalRing_of_isLocalHom
