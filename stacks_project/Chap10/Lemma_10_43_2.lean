/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.FilteredColimits
public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Closure Properties of Geometrically Reduced Algebras

Lemma 10.43.2 (Tag 030T) is organized as canonical recalls.  The reusable
owners are stated at the injective-map, filtered-colimit, and arbitrary-
localization levels; the textbook ordered directed systems are instances of
the categorical filtered-colimit formulation.

@stack 030T
-/

/- Lemma 10.43.2 (1) (Tag 030T): subalgebra closure is the canonical injective-map theorem. -/
@[stacks 030T]
#check @Algebra.IsGeometricallyReduced.of_injective

/- Lemma 10.43.2 (2) (Tag 030T): finitely generated subalgebra closure is the canonical theorem. -/
@[stacks 030T]
#check @Algebra.IsGeometricallyReduced.of_forall_fg

/- Lemma 10.43.2 (3) (Tag 030T): directed systems are covered by the categorical filtered-colimit
owner; the cocone-level theorem is the reusable API and the canonical theorem is a convenience. -/
@[stacks 030T]
#check @Algebra.IsGeometricallyReduced.of_isColimit_filtered
@[stacks 030T]
#check @Algebra.IsGeometricallyReduced.colimit_of_isFilteredOrEmpty

/- Lemma 10.43.2 (4) (Tag 030T): arbitrary localization closure is owned by ReasLib. -/
@[stacks 030T]
#check @Algebra.IsGeometricallyReduced.of_isLocalization
#check @Algebra.IsGeometricallyReduced.of_isLocalization_of
#check @Localization.instIsGeometricallyReduced
