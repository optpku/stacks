/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import ReasLib.CategoryTheory.Homology.ExactCouple.Derived
public import ReasLib.CategoryTheory.Homology.ShortComplex.Cycles
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageFiltration
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bockstein Exact Couples

This module owns the exact couple and zero-based spectral sequence attached to a monomorphism of
one-object homological complexes.  It is independent of the textbook chapter in which the
construction first occurs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex.HomologySequence
open scoped CategoryTheory SpectralSequence
open CategoryTheory.ExactCouple.Derived

noncomputable section

universe u v

namespace CategoryTheory
namespace HomologicalComplex.Bockstein

open ExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : HomologicalComplex C (ComplexShape.refl PUnit.{1})}
variable (α : A ⟶ A)

/-- The quotient short complex `A ⟶ A ⟶ cokernel α` underlying a Bockstein exact couple. -/
@[stacks 011Z "quotient short complex"]
noncomputable abbrev quotientShortComplex :
    ShortComplex (HomologicalComplex C (ComplexShape.refl PUnit.{1})) :=
  ShortComplex.mk α (cokernel.π α) (cokernel.condition α)

/-- The canonical short exact sequence `A ⟶ A ⟶ cokernel α` attached to a monomorphism. -/
@[stacks 011Z "quotient short exact sequence"]
theorem quotientShortExact [Mono α] :
    (quotientShortComplex α).ShortExact := sorry

/-- The connecting morphism in homology for the quotient short exact sequence. -/
@[stacks 011Z "Bockstein connecting morphism"]
noncomputable def connecting (h : (quotientShortComplex α).ShortExact) :
    HomologicalComplex.homology (cokernel α) PUnit.unit ⟶
      HomologicalComplex.homology A PUnit.unit :=
  h.δ PUnit.unit PUnit.unit rfl

/-- The Bockstein exact couple from the periodic homology sequence of
`A ⟶ A ⟶ cokernel α`. -/
@[stacks 011Z]
noncomputable def exactCouple (h : (quotientShortComplex α).ShortExact) :
    CategoryTheory.ExactCouple C :=
  { A := HomologicalComplex.homology A PUnit.unit
    E := HomologicalComplex.homology (cokernel α) PUnit.unit
    α := HomologicalComplex.homologyMap α PUnit.unit
    f := connecting α h
    g := HomologicalComplex.homologyMap (cokernel.π α) PUnit.unit
    f_comp_α := sorry
    g_comp_f := sorry
    α_comp_g := sorry
    exact_f_α := sorry
    exact_g_f := sorry
    exact_α_g := sorry }

namespace ExactCouple

/-- The outer endomorphism of the Bockstein exact couple is the map induced by `α` in
homology. -/
@[simp]
theorem alpha (h : (quotientShortComplex α).ShortExact) :
    (exactCouple α h).α = HomologicalComplex.homologyMap α PUnit.unit := sorry

/-- The map from the Bockstein page object to its outer object is the connecting homomorphism of
the quotient short exact sequence. -/
@[simp]
theorem f (h : (quotientShortComplex α).ShortExact) :
    (exactCouple α h).f = connecting α h := sorry

/-- The map from the outer object to the Bockstein page object is induced by the quotient map. -/
@[simp]
theorem g (h : (quotientShortComplex α).ShortExact) :
    (exactCouple α h).g = HomologicalComplex.homologyMap (cokernel.π α) PUnit.unit := sorry

end ExactCouple

/-- Definition 12.22.5: the zero-based Bockstein spectral sequence associated to `α`.  Its
zeroth page is `cokernel α`, and its positive pages are those of `exactCouple α`. -/
@[stacks 011Z]
noncomputable def spectralSequence (h : (quotientShortComplex α).ShortExact) (K : Construction C) :
    SpectralSequence C (fun _ : ℤ ↦ ComplexShape.refl PUnit.{1}) 0 :=
  SpectralSequence.Page.Zero.ofOne (cokernel α)
    (K.associatedSpectralSequence (exactCouple α h)) (fun _ ↦ Iso.refl _)

namespace Page

/-- Every positive Bockstein page is the corresponding page of its associated exact-couple
spectral sequence. -/
@[stacks 011Z "positive-page comparison"]
theorem eq_associated (h : (quotientShortComplex α).ShortExact) (K : Construction C)
    (r : ℤ) (hr : 1 ≤ r) :
    (spectralSequence α h K).page r (zero_le_one.trans hr) =
      (K.associatedSpectralSequence (exactCouple α h)).page r hr := sorry

end Page

section

variable (h : (quotientShortComplex α).ShortExact) (K : Construction C)

/-- The zeroth Bockstein page is the quotient differential object. -/
@[simp]
theorem page_zero :
    (spectralSequence α h K).page 0 = cokernel α := sorry

/-- The unique object on the zeroth page is the quotient object. -/
@[simp]
theorem page_zero_obj :
    ((spectralSequence α h K).page 0).X PUnit.unit = (cokernel α).X PUnit.unit := sorry

/-- The zeroth differential is induced on the quotient complex. -/
@[simp]
theorem page_zero_d :
    ((spectralSequence α h K).page 0).d PUnit.unit PUnit.unit =
      (cokernel α).d PUnit.unit PUnit.unit := sorry

namespace ZeroPage

/-- The cycle subobject of the quotient differential object on the zeroth page. -/
@[stacks 011Z "zero-page cycles"]
noncomputable abbrev cycles :
    Subobject ((cokernel α).X PUnit.unit) :=
  kernelSubobject ((cokernel α).dFrom PUnit.unit)

end ZeroPage

/-- Definition 12.22.5: the zero-based Bockstein cycle filtration on the quotient page. -/
@[stacks 011Z]
noncomputable abbrev cycle : ℕ → Subobject ((cokernel α).X PUnit.unit) :=
  ((K.associatedSpectralSequence (exactCouple α h)).homologyPageTower PUnit.unit).preimageCycle
    ((cokernel α).sc PUnit.unit) (Iso.refl _)

/-- Definition 12.22.5: the zero-based Bockstein boundary filtration on the quotient page. -/
@[stacks 011Z]
noncomputable abbrev boundary : ℕ → Subobject ((cokernel α).X PUnit.unit) :=
  ((K.associatedSpectralSequence (exactCouple α h)).homologyPageTower PUnit.unit).preimageBoundary
    ((cokernel α).sc PUnit.unit) (Iso.refl _)

namespace Cycle

/-- The positive Bockstein cycle stages are pulled back from the associated exact-couple spectral
sequence. -/
@[simp]
theorem succ (r : ℕ) :
    cycle α h K (r + 1) =
      ShortComplex.Cycles.preimageOfIso ((cokernel α).sc PUnit.unit) (Iso.refl _)
        ((K.associatedSpectralSequence (exactCouple α h)).cycle PUnit.unit
          (HomologyPageTower.pageIndex r)) := sorry

end Cycle

namespace Boundary

/-- The positive Bockstein boundary stages are pulled back from the associated exact-couple
spectral sequence. -/
@[simp]
theorem succ (r : ℕ) :
    boundary α h K (r + 1) =
      ShortComplex.Cycles.preimageOfIso ((cokernel α).sc PUnit.unit) (Iso.refl _)
        ((K.associatedSpectralSequence (exactCouple α h)).boundary PUnit.unit
          (HomologyPageTower.pageIndex r)) := sorry

end Boundary

/-- The zero-stage Bockstein cycle piece is the whole quotient object. -/
@[simp]
theorem cycle_zero : cycle α h K 0 = ⊤ := sorry

/-- The zero-stage Bockstein boundary piece is zero. -/
@[simp]
theorem boundary_zero : boundary α h K 0 = ⊥ := sorry

/-- The first Bockstein page is the homology of the quotient differential object. -/
theorem page_one :
    ((spectralSequence α h K).page 1).X PUnit.unit =
      HomologicalComplex.homology (cokernel α) PUnit.unit := sorry

end

end HomologicalComplex.Bockstein
end CategoryTheory
