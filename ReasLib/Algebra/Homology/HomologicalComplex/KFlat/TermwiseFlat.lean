/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Flat.Isomorphism
public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat.Isomorphism
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat homological complexes with flat terms

This file owns the conjunction used by flat-resolution constructions before passage to a
homotopy or derived category.  Keeping it as an `ObjectProperty` makes closure and inverse-image
APIs available without introducing application-specific `Good` classes.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace HomologicalComplex.KFlat

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable {I : Type*} [AddMonoid I] [DecidableEq I]
variable (c : ComplexShape I) [c.TensorSigns]

/-- The object property of homological complexes that are both K-flat and termwise flat. -/
@[stacks 06YY "homological-complex owner"]
def termwiseFlat : ObjectProperty (HomologicalComplex C c) :=
  fun K ↦ K.IsKFlat ∧ K.IsTermwiseFlat

/-- Membership in `HomologicalComplex.KFlat.termwiseFlat` is exactly the conjunction of
K-flatness and termwise flatness. -/
theorem termwiseFlat_iff (K : HomologicalComplex C c) :
    termwiseFlat c K ↔ K.IsKFlat ∧ K.IsTermwiseFlat := sorry

/-- A K-flat termwise-flat homological complex is K-flat. -/
theorem termwiseFlat.isKFlat {K : HomologicalComplex C c}
    (hK : termwiseFlat c K) : K.IsKFlat := sorry

/-- A K-flat termwise-flat homological complex is termwise flat. -/
theorem termwiseFlat.isTermwiseFlat {K : HomologicalComplex C c}
    (hK : termwiseFlat c K) : K.IsTermwiseFlat := sorry

namespace termwiseFlat

/-- K-flat termwise-flat complexes are invariant under isomorphisms. -/
instance isClosedUnderIsomorphisms :
    (termwiseFlat (C := C) c).IsClosedUnderIsomorphisms := sorry

end termwiseFlat

end HomologicalComplex.KFlat
