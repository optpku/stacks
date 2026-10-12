/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived scalar extension along polynomial evaluation

The derived self-intersection of the zero section `R[X] → R` splits into an object and its
shift.

@stack 065F
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat.DerivedExtension.Polynomial

/-- Lemma 15.82.1 (065F): after viewing a derived `R`-complex over `R[X]` through evaluation at
zero, derived extension back to `R` is isomorphic to the complex together with its shift. -/
@[stacks 065F "derived self-intersection of polynomial evaluation at zero"]
theorem evalZero_selfIntersection
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat R)) :
    IsIsomorphic
      ((ModuleCat.derivedExtensionOfScalars (Polynomial.evalRingHom (0 : R))).obj
        ((ModuleCat.derivedRestrictionOfScalars
          (Polynomial.evalRingHom (0 : R))).obj K))
      (K ⊞ K⟦(1 : ℤ)⟧) := sorry

end CategoryTheory.ModuleCat.DerivedExtension.Polynomial
