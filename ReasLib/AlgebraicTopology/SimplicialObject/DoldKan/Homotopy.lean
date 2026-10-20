/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy.NormalizedMoore
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 01A4

# Dold--Kan fullness on simplicial homotopies

Under the Dold--Kan equivalence, every chain homotopy between maps of normalized Moore complexes
is induced by a directed simplicial homotopy. The canonical API records this as surjectivity of
the existing normalized-Moore homotopy comparison map.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Homotopy

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} {a b : U ⟶ V}

namespace normalizedMoore

/-- The normalized-Moore homotopy comparison is surjective: every chain homotopy between the
normalized maps of two simplicial morphisms is induced by a directed simplicial homotopy. -/
@[stacks 01A4]
theorem surjective :
    Function.Surjective
      (Homotopy.normalizedMoore (A := A) (a := a) (b := b)) := sorry

/-- Pointwise form of surjectivity, oriented so that the prescribed chain homotopy appears on
the left of the comparison equality. -/
@[stacks 01A4 "prescribed normalized-Moore homotopy"]
theorem exists_eq
    (N : _root_.Homotopy
      ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    ∃ H : SimplicialObject.Homotopy a b,
      N = H.normalizedMoore := sorry

end normalizedMoore

end CategoryTheory.SimplicialObject.Homotopy
