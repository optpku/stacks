/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence and finite presentation on a ringed site

When the structure module is coherent, coherence of a module sheaf is equivalent to Mathlib's
local finite-presentation predicate.  The reverse implication is exposed separately so callers do
not need to unpack an equivalence.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

namespace IsCoherent

/-- Finite presentation implies coherence when the structure module is coherent.  This is a
theorem, rather than an instance, to avoid a typeclass cycle with
`IsCoherent.isFinitePresentation`. -/
@[stacks 01BZ "finite presentation implies coherence"]
theorem ofFinitePresentation [IsCoherent (unit R)]
    (M : SheafOfModules.{w} R) [M.IsFinitePresentation] : M.IsCoherent := sorry

/-- Lemma 17.12.5 (01BZ), generalized to a ringed site: if the structure module is coherent, a
module sheaf is coherent exactly when it is finitely presented. -/
@[stacks 01BZ]
theorem iff_finitePresentation [IsCoherent (unit R)]
    (M : SheafOfModules.{w} R) : M.IsCoherent ↔ M.IsFinitePresentation := sorry

end IsCoherent

end SheafOfModules
