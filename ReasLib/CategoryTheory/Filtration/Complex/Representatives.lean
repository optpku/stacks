/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Cohomology
public import ReasLib.CategoryTheory.Filtration.Morphism.PageRepresentatives
public import ReasLib.Order.Filtration

/-!
# Cohomology Representatives of a Filtered Complex

This leaf owns the subobjects in a term of a filtered cochain complex that represent intrinsic
cycles, boundaries, and the induced cohomology filtration.  They do not depend on a spectral
sequence or a convergence hypothesis.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace FilteredComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Cohomology.Representative

/-- The intrinsic boundary representative for the graded piece of `H^n(K)`. -/
@[stacks 012V "intrinsic cohomology boundary representative"]
abbrev boundary (K : FilteredComplex C) (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (K.d (n - 1) n).imageRepresentative p

/-- The intrinsic cycle representative for the graded piece of `H^n(K)`. -/
@[stacks 012V "intrinsic cohomology cycle representative"]
abbrev cycle (K : FilteredComplex C) (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (K.d n (n + 1)).kernelRepresentative p

/-- The representative in `K^n` of the `p`-th stage of the filtration induced on cohomology. -/
@[stacks 012V "induced cohomology filtration representative"]
def filtration (K : FilteredComplex C) (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  Order.Filtration.Subquotient.representative (K.X n).filtration
    (imageSubobject ((K.d (n - 1) n).hom)) (kernelSubobject ((K.d n (n + 1)).hom)) p

end Cohomology.Representative

end FilteredComplex
end CategoryTheory
