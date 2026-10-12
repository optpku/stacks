/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison with monoidal K-flatness

@stack 06XZ

In the carrier universe of the base ring, the universe-polymorphic tensor bifunctor and the
monoidal tensor product define the same K-flatness predicate.
-/

@[expose] public section

universe u

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- For complexes of modules in the base-ring universe, K-flatness over `R` agrees with
K-flatness for the monoidal tensor product on `ModuleCat R`. -/
@[stacks 06XZ "comparison with monoidal K-flatness"]
theorem isKFlatOver_iff_isKFlat (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    K.IsKFlatOver ↔ K.IsKFlat := sorry

end CochainComplex
