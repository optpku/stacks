/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Cohomology
public import ReasLib.CategoryTheory.Linear.PrincipalPower.ModuleCat
public import ReasLib.RingTheory.Ideal.Principal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of principal derived completion

This file records the two nonzero cohomological degrees of the derived completion of a module
with respect to a principal ideal.  It also gives the resulting short exact row for the
cohomology of the principal derived completion of an arbitrary object of `D(A)`.

@stack 0BKG
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem

universe u

-- Local instance justification (defeq pin): use the standard derived-category localization in
-- both the completion object and all of its cohomology objects.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory.PrincipalCompletion

variable {A : Type u} [CommRing A]

/-- The derived completion of a module placed in cohomological degree zero. -/
@[stacks 0BKG "principal derived completion of a module"]
abbrev ofModule (f : A) (M : ModuleCat.{u} A) :
    DerivedCategory (ModuleCat.{u} A) :=
  DerivedCategory.derivedCompletionOf (principalIdeal f) (principalIdeal_fg f)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj M)

/-- Degree-`p` cohomology of the principal derived completion of a module. -/
@[stacks 0BKG "principal derived-completion module cohomology"]
abbrev moduleHomology (f : A) (M : ModuleCat.{u} A) (p : ℤ) : ModuleCat.{u} A :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj (ofModule f M)

/-- Example 15.94.5 (1) (Stacks `0BKG`): degree `-1` cohomology of the principal derived
completion of `M` is the principal Tate module of `M`. -/
@[stacks 0BKG "(1), degree minus one as the Tate module"]
theorem moduleHomologyNegOne_isIsomorphic_tateModule (f : A) (M : ModuleCat.{u} A) :
    IsIsomorphic (moduleHomology f M (-1)) (ModuleCat.PrincipalPower.tateModule f M) := sorry

/-- Example 15.94.5 (2) (Stacks `0BKG`): degree-zero cohomology of the principal derived
completion of `M` lies in the Milnor short exact sequence between the first derived limit of
principal-power torsion and the principal-adic completion of `M`. -/
@[stacks 0BKG "(2), degree-zero Milnor short exact sequence"]
theorem moduleHomologyZero_shortExact (f : A) (M : ModuleCat.{u} A) :
    ∃ (ι : firstDerivedLimit (ModuleCat.PrincipalPower.torsionSystem f M) ⟶
        moduleHomology f M 0)
      (π : moduleHomology f M 0 ⟶
        limit (ModuleCat.PrincipalPower.quotientSystem f M))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

/-- Example 15.94.5 (3) (Stacks `0BKG`): the principal derived completion of a module has
cohomology only in degrees `-1` and `0`. -/
@[stacks 0BKG "(3), cohomological amplitude"]
theorem moduleHomology_isZero_of_ne_zero_or_negOne
    (f : A) (M : ModuleCat.{u} A) (p : ℤ) (hp0 : p ≠ 0) (hpneg1 : p ≠ -1) :
    IsZero (moduleHomology f M p) := sorry

/-- Example 15.94.5 (4) (Stacks `0BKG`): for `K ∈ D(A)`, degree-`p` cohomology of its
principal derived completion lies in a short exact sequence whose left term is degree-zero
cohomology of the completed module `H^p(K)` and whose right term is the Tate module of
`H^(p+1)(K)`. -/
@[stacks 0BKG "(4), cohomology short exact sequence"]
theorem cohomology_shortExact
    (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (p : ℤ) :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A)
    ∃ (ι : moduleHomology f ((H p).obj K) 0 ⟶
        (H p).obj
          (DerivedCategory.derivedCompletionOf (principalIdeal f) (principalIdeal_fg f) K))
      (π : (H p).obj
          (DerivedCategory.derivedCompletionOf (principalIdeal f) (principalIdeal_fg f) K) ⟶
        ModuleCat.PrincipalPower.tateModule f ((H (p + 1)).obj K))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end CategoryTheory.DerivedCategory.PrincipalCompletion
