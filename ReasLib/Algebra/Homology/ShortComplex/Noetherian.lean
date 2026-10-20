/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Noetherian homology modules of short complexes

The concrete `moduleCatLeftHomologyData.K` and `.H` projections are opaque to typeclass search,
even though they are a submodule and a quotient of the middle term.  This file supplies the
canonical Noetherian instances for the concrete and abstract homology models.  Mathlib's standard
`IsNoetherian.finite` instance then supplies `Module.Finite` without local instance pins.
@stack 0G3K
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.ShortComplex.ModuleCatNoetherian

variable {A : Type u} [Ring A]

/-- The concrete cycle module inherits Noetherianity from the middle term. -/
@[stacks 0G3K "Noetherian concrete cycles of a short complex"]
instance leftHomologyDataK
    (S : ShortComplex (ModuleCat.{v} A)) [IsNoetherian A (S.X₂ : Type v)] :
    IsNoetherian A (S.moduleCatLeftHomologyData.K : Type v) := sorry

/-- The concrete left-homology module inherits Noetherianity from the middle term. -/
@[stacks 0G3K "Noetherian concrete homology of a short complex"]
instance leftHomologyDataH
    (S : ShortComplex (ModuleCat.{v} A)) [IsNoetherian A (S.X₂ : Type v)] :
    IsNoetherian A (S.moduleCatLeftHomologyData.H : Type v) := sorry

/-- The categorical cycles inherit Noetherianity from the middle term. -/
@[stacks 0G3K "Noetherian categorical cycles of a short complex"]
instance cycles
    (S : ShortComplex (ModuleCat.{v} A)) [IsNoetherian A (S.X₂ : Type v)] :
    IsNoetherian A (S.cycles : Type v) := sorry

/-- The categorical homology inherits Noetherianity from the middle term. -/
@[stacks 0G3K "Noetherian categorical homology of a short complex"]
instance homology
    (S : ShortComplex (ModuleCat.{v} A)) [IsNoetherian A (S.X₂ : Type v)] :
    IsNoetherian A (S.homology : Type v) := sorry

section Synthesis

variable (S : ShortComplex (ModuleCat.{v} A)) [IsNoetherian A (S.X₂ : Type v)]

#synth Module.Finite A (S.moduleCatLeftHomologyData.K : Type v)
#synth Module.Finite A (S.moduleCatLeftHomologyData.H : Type v)
#synth Module.Finite A (S.cycles : Type v)
#synth Module.Finite A (S.homology : Type v)

end Synthesis

end CategoryTheory.ShortComplex.ModuleCatNoetherian
