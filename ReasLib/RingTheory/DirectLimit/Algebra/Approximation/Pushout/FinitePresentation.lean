/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Pushout.Core
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentation through approximation pushouts

This leaf records the ring-level finite-presentation consequence of a
bijective stage base change.  It is independent of module-system data and is
therefore the semantic owner for both finite-type and arbitrary directed
module-system applications.
-/

@[expose] public section

universe u v

namespace Ring.DirectLimit.Algebra.Approximation.Hom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- A finitely presented map at one stage induces a finitely presented
limiting map when the stage base-change maps are bijective.  The proof uses
the final pushout square and finite-presentation stability under base change. -/
@[stacks 00R0 "directed approximation final finite presentation"]
theorem final_finitePresentation (A : Hom f)
    (hbaseChange : A.baseChange_bijective) (i : A.index)
    (hstageMap : (A.map i).FinitePresentation) :
    f.FinitePresentation := sorry

end Ring.DirectLimit.Algebra.Approximation.Hom
