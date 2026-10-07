module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import ReasLib.CategoryTheory.Monoidal.Flat.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat opcycles of a termwise-flat complex

@stack 08G0

The reusable owner is the canonical opcycles object.  Raw cokernels of individual differentials
are obtained from the standard opcycles-cokernel isomorphism at source-facing boundaries.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
variable [∀ X : C, PreservesFiniteColimits (tensorRight X)]

/-- A termwise-flat cochain complex has flat opcycles in degree `a` when tensoring its
three-term segment ending in degree `a` is exact at degree `a - 1`. -/
@[stacks 08G0 "abstract opcycles criterion"]
theorem IsTermwiseFlat.isFlat_opcycles
    (K : CochainComplex C ℤ) (hFlat : K.IsTermwiseFlat) (a : ℤ)
    (hExact : ∀ G : C, ((K.sc (a - 1)).map (tensorRight G)).Exact) :
    IsFlat (K.opcycles a) := sorry

end HomologicalComplex
