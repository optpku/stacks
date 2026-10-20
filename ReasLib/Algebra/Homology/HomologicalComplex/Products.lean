/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Products and homology of homological complexes

This leaf owns the canonical comparison from the homology of a termwise product of
homological complexes to the product of their homology objects.  The comparison is
defined by its composites with the product projections; exactness is used only to
prove that this explicit morphism is invertible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u uI uι

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} {c : ComplexShape ι} {I : Type uI}
variable [HasProductsOfShape I C]

/-- The canonical comparison from the homology of a termwise product of complexes to the
product of their homology objects. -/
@[stacks 07KC]
noncomputable def piHomologyComparison (K : I → HomologicalComplex C c) (i : ι) :
    (∏ᶜ K).homology i ⟶ ∏ᶜ fun j ↦ (K j).homology i :=
  Pi.lift fun j ↦ homologyMap (Pi.π K j) i

/-- The homology-product comparison is characterized by the homology maps of the termwise
product projections. -/
@[stacks 07KC, simp, reassoc (attr := simp)]
theorem piHomologyComparison_π (K : I → HomologicalComplex C c) (i : ι) (j : I) :
    piHomologyComparison K i ≫ Pi.π (fun k ↦ (K k).homology i) j =
      homologyMap (Pi.π K j) i := sorry

/-- Exact products make the canonical comparison from homology of a termwise product to the
product of homology objects invertible. -/
@[stacks 07KC]
instance piHomologyComparison_isIso (K : I → HomologicalComplex C c) (i : ι)
    [HasExactLimitsOfShape (Discrete I) C] :
    IsIso (piHomologyComparison K i) := sorry

end HomologicalComplex
