/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Short exactness of degreewise split complexes

A chosen splitting in every degree makes a short complex of homological complexes short exact.
This file isolates that shape-independent bridge from the chain- and cochain-specific connecting
map constructions.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

namespace CategoryTheory.ShortComplex.DegreewiseSplitting

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type*} {c : ComplexShape ι}
variable {S : ShortComplex (HomologicalComplex C c)}

/-- A chosen degreewise splitting is short exact after evaluation in any degree. -/
@[stacks 014I "evaluated degreewise splitting is short exact"]
theorem shortExactApp (σ : DegreewiseSplitting S) (i : ι) :
    (S.degreewise i).ShortExact := sorry

/-- A short complex of homological complexes with a chosen splitting in every degree is short
exact. -/
@[stacks 014I "degreewise splitting is short exact"]
theorem shortExact (σ : DegreewiseSplitting S) : S.ShortExact := sorry

end CategoryTheory.ShortComplex.DegreewiseSplitting
