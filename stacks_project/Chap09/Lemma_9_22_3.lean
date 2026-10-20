/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Galois.Profinite
import StacksCheckRecall

@[expose] public section

/- Lemma 9.22.3 (Tag 0BU2): the finite Galois intermediate fields form the canonical directed
indexing system for the inverse system of finite Galois groups, whose profinite limit is
`Gal(L / K)`. -/
universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]

@[stacks 0BU2]
#check FiniteGaloisIntermediateField
#synth Lattice (FiniteGaloisIntermediateField K L)
#check FiniteGaloisIntermediateField.adjoin
#check FiniteGaloisIntermediateField.subset_adjoin
#check finGaloisGroupMap
#check finGaloisGroupFunctor
#check InfiniteGalois.asProfiniteGaloisGroupFunctor
#check InfiniteGalois.algEquivToLimit_continuous
#check InfiniteGalois.continuousMulEquivToLimit
#check InfiniteGalois.profiniteGalGrpIsoLimit
