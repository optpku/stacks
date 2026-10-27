/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Basic
public import ReasLib.Algebra.PolynomialSite.Differentials
public import ReasLib.CategoryTheory.Sites.CategoryHomology.Module

/-!
# Polynomial-site homology and the cotangent complex

For a commutative algebra map, polynomial-site homology of the differential sheaf computes the
corresponding negative cohomology of the cotangent complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Algebra
open CommAlgCat.Over.Polynomial.Site
open CategoryTheory.CategoryHomology

noncomputable section

universe u

namespace Algebra.CotangentComplex

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasProjectiveResolutions ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]

/-- Category homology of the polynomial-site differential sheaf in degree `n` is the
`(-n)`-th cohomology object of the cotangent complex. -/
theorem polynomialSite_homology_isIsomorphic (n : ℕ) :
    IsIsomorphic (moduleHomology (omegaSheaf A B) n)
      ((cotangentComplex A B).homology (-n)) :=
  sorry

end Algebra.CotangentComplex
