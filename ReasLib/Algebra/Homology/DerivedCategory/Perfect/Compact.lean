/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.CategoryTheory.Preadditive.CompactObject
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Compact Objects in Derived Categories of Modules

@stack 07LT

This leaf owns the intrinsic identification of perfect complexes with compact objects.  Keeping
the comparison beside `DerivedCategory.IsPerfect` lets downstream Morita and duality APIs use
either formulation without importing a textbook chapter.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace DerivedCategory

variable {R : Type u} [Ring R]

/-- Proposition 15.79.3 (07LT): an object of `D(R)` is perfect if and only if it is compact. -/
@[stacks 07LT "perfect complexes are compact"]
theorem isPerfect_iff_isCompactObject (K : DerivedCategory (ModuleCat R)) :
    K.IsPerfect ↔ IsCompactObject K := sorry

/-- A perfect object of `D(R)` is compact. -/
theorem IsPerfect.isCompactObject {K : DerivedCategory (ModuleCat R)}
    (hK : K.IsPerfect) : IsCompactObject K := sorry

/-- A compact object of `D(R)` is perfect. -/
theorem isPerfect_of_isCompactObject {K : DerivedCategory (ModuleCat R)}
    (hK : IsCompactObject K) : K.IsPerfect := sorry

end DerivedCategory
