/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import ReasLib.CategoryTheory.Monoidal.Flat
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Termwise-flat homological complexes

Termwise flatness is defined once for complexes in an arbitrary monoidal category.  Module and
sheaf specializations can use this owner instead of rebuilding degreewise predicates.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C] [MonoidalCategory C]
variable {ι : Type w} {c : ComplexShape ι}

/-- A homological complex in a monoidal category is termwise flat when every component is a flat
object.  This is an explicit property rather than a typeclass: downstream results should name the
termwise-flatness proof instead of asking typeclass search to reconstruct it. -/
@[stacks 06YY "shape-general termwise-flat predicate"]
def IsTermwiseFlat (K : HomologicalComplex C c) : Prop :=
  ∀ i : ι, IsFlat (K.X i)

namespace IsTermwiseFlat

/-- Every component of a termwise-flat complex is flat. -/
theorem isFlat {K : HomologicalComplex C c} (hK : IsTermwiseFlat K) (i : ι) :
    IsFlat (K.X i) := sorry

end IsTermwiseFlat

/-- Termwise flatness unfolds to flatness in every degree. -/
theorem isTermwiseFlat_iff (K : HomologicalComplex C c) :
    IsTermwiseFlat K ↔ ∀ i : ι, IsFlat (K.X i) := sorry

/-- Degreewise flatness constructs the termwise-flat predicate. -/
theorem isTermwiseFlat_of_forall
    (K : HomologicalComplex C c) (hK : ∀ i : ι, IsFlat (K.X i)) :
    IsTermwiseFlat K := sorry

end HomologicalComplex
