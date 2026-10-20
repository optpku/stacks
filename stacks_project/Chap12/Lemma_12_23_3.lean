/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.SpectralSequence
import StacksCheckRecall

/-!
# Lemma 12.23.3

Source-facing check for the first differential of the spectral sequence of a filtered
differential object.  The shared owner uses the canonical two-step quotient sequence for an
arbitrary filtered homological complex.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
variable {E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0}
variable (A : HomologicalComplex.Filtered.Association K E) (p : ℤ)

/- Lemma 12.23.3 [012D]: under the canonical page-one comparisons,
`A.pageOne_d_eq_boundaryMap p` identifies the differential with the connecting morphism of
`HomologicalComplex.Filtered.TwoStep.shortExact K p`. -/
@[stacks 012D]
#check (A.pageOne_d_eq_boundaryMap p :
  CommSq
    ((E.page 1).d p (p + 1))
    ((HomologicalComplex.Filtered.Association.PageOne.iso A p).hom)
    ((HomologicalComplex.Filtered.Association.PageOne.iso A (p + 1)).hom)
    (HomologicalComplex.Filtered.TwoStep.boundary K p rfl))
