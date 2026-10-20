/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import ReasLib.Topology.Compactification.StoneCech
import StacksCheckRecall

@[expose] public section

open Set Topology OnePoint

universe u

variable {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

/- Lemma 5.25.2 (1): the one-point compactification contains `X` as an open subspace. -/
@[stacks 090A "the one-point compactification contains X as an open subspace"]
#check OnePoint.isOpenEmbedding_coe

/- Lemma 5.25.2 (2): the one-point compactification is compact. -/
@[stacks 090A "the one-point compactification is quasi-compact"]
#check (inferInstance : CompactSpace (OnePoint X))

/- Lemma 5.25.2 (3): the one-point compactification is Hausdorff. -/
@[stacks 090A "the one-point compactification is Hausdorff"]
#check (inferInstance : T2Space (OnePoint X))

/- Lemma 5.25.2 (4): the complement of the ordinary locus is the point at infinity. -/
@[stacks 090A "the complement of X in its one-point compactification is a singleton"]
#check OnePoint.compl_range_coe

/- Lemma 5.25.2 (5): the Stone-Cech unit is an open embedding for a locally compact Hausdorff
space. -/
@[stacks 090A "the Stone-Cech unit identifies X with an open subspace"]
#check StoneCech.isOpenEmbedding_unit
