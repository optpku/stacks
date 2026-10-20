/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RegularLocalRing.Parameters.Perturbation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.126.4

@stack 0BWV

The two-dimensional statement is the singleton-tail specialization of the
shared high-order perturbation API.
-/

/- Lemma 15.126.4, clauses (a)-(b): the same witnesses give a two-element parameter system and
stability under every sufficiently high-order head perturbation. -/
@[stacks 0BWV "Lemma 15.126.4, clauses (a)-(b)"]
#check @IsLocalRing.IsSystemOfParameters.exists_cons_singleton_stable

#check @IsLocalRing.IsSystemOfParameters.StableUnderHeadPerturbation

/- Lemma 15.126.4 (b), parameter clause: every allowed perturbation remains a system of
parameters. -/
@[stacks 0BWV "Lemma 15.126.4 (b), parameter clause"]
#check @IsLocalRing.IsSystemOfParameters.StableUnderHeadPerturbation.isSystemOfParameters

/- Lemma 15.126.4 (b), length clause: the corresponding parameter quotients have equal length. -/
@[stacks 0BWV "Lemma 15.126.4 (b), length clause"]
#check @IsLocalRing.IsSystemOfParameters.StableUnderHeadPerturbation.length_eq
