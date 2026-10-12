/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Invertible
import StacksCheckRecall

/-!
# Lemma 15.127.4

@stack 0FNT
-/

@[expose] public section

/- Lemma 15.127.4, equivalence: invertibility is equivalent to being locally a shift of the
localized unit. -/
@[stacks 0FNT "Lemma 15.127.4, equivalence"]
#check @DerivedCategory.isInvertibleObject_iff_localizationAway_iso_shift

/- Lemma 15.127.4 (a): invertible derived objects are perfect. -/
@[stacks 0FNT "Lemma 15.127.4 (a)"]
#check @DerivedCategory.IsPerfect.of_isInvertibleObject

/- Lemma 15.127.4 (b): an invertible derived object splits as the finite direct sum of its
shifted cohomology. -/
@[stacks 0FNT "Lemma 15.127.4 (b)"]
#check @DerivedCategory.Invertible.existsShiftedCohomologyDecomposition

/- Lemma 15.127.4 (c): every cohomology module of an invertible derived object is finite
projective. -/
@[stacks 0FNT "Lemma 15.127.4 (c)"]
#check @DerivedCategory.Invertible.homologyFiniteProjective

/- Lemma 15.127.4 (d): the base ring decomposes into factors on which the corresponding
cohomology module is invertible. -/
@[stacks 0FNT "Lemma 15.127.4 (d)"]
#check @DerivedCategory.Invertible.existsRingProductDecomposition
