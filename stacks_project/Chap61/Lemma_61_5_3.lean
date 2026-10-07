module

public import stacks_project.Chap61.Lemma_61_5_3_Ring
public import stacks_project.Chap61.Lemma_61_5_3_WLocal
import StacksCheckRecall

@[expose] public section

open Algebra.WLocalHull
open AlgebraicGeometry.WLocal.Construction

/- Lemma 61.5.3 (1): A → A_w is ind-Zariski and faithfully flat. -/
@[stacks 0975] #check algebraMap_indZariski
@[stacks 0975] #check algebraMap_faithfullyFlat

/- Lemma 61.5.3 (2): X_w → X induces a bijection Z → X. -/
@[stacks 0975] #check bijective_closedToSpec

/- Lemma 61.5.3 (3): Z is the set of closed points of X_w. -/
@[stacks 0975] #check range_closedι_eq_closedPoints

/- Lemma 61.5.3 (4): Z is a reduced scheme. -/
@[stacks 0975] #check instIsReduced_closedSubscheme

/- Lemma 61.5.3 (5): every point of X_w specializes to a unique point of Z. -/
@[stacks 0975] #check existsUnique_specializes_mem_range_closedι

/- Lemma 61.5.3 (6): in particular X_w is w-local. -/
@[stacks 0975] #check AlgebraicGeometry.WLocal.Construction.instWLocalSpace
