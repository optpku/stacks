module

public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Basic
public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
public import ReasLib.CategoryTheory.Filtration.Complex.Quotient
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Realization
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded.FromZero
public import ReasLib.CategoryTheory.Shift.ShiftedHom.AddCommGrp
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-!
# Filtered Extension Spectral Sequences

This file states the reusable target- and source-filtered forms of extension spectral
sequences.  Specializations to canonical filtrations live in the sibling `Target` and `Source`
modules.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated ShiftedHom
open scoped DerivedExt

noncomputable section

universe t w v u

namespace CategoryTheory.DerivedCategory.Ext

section Derived

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{t} A]

namespace Target

/-- Eventual vanishing of `Ext⁽n⁾(M, F^p K)` as the target filtration index tends to
`+∞`. -/
@[stacks 0G1X "target-filtration vanishing"]
def VanishesAbove (M : DerivedCategory A) (K : FilteredComplex A) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
    IsZero (addCommGrp M (DerivedCategory.Q.obj (K.stage p)) n)

/-- Eventual stabilization of the canonical maps
`Ext⁽n⁾(M, F^p K) ⟶ Ext⁽n⁾(M, K)` as the target filtration index tends to `-∞`. -/
@[stacks 0G1X "target-filtration stabilization"]
def StabilizesBelow (M : DerivedCategory A) (K : FilteredComplex A) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ →
    IsIso (ShiftedHom.postcomp M (DerivedCategory.Q.map (K.stageInclusion p)) n)

/-- A genuine filtered-complex model for the target-filtered Ext spectral sequence.  Association
links the spectral sequence to `F`; the remaining fields identify its first page and abutment and
state the target convergence criterion. -/
@[stacks 0G1X "target-filtered Ext spectral sequence"]
structure IsSpectralSequence (M : DerivedCategory A) (K : FilteredComplex A)
    (F : FilteredComplex AddCommGrpCat.{t})
    (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0) : Prop
    extends FilteredComplex.SpectralSequence.Realizes F E
      (fun n => addCommGrp M (DerivedCategory.Q.obj K.underlying) n) where
  /-- The first page is `Ext⁽p+q⁾(M, gr^p K)`. -/
  pageOne : ∀ p q : ℤ,
    Nonempty ((E.page 1).X (p, q) ≅
      addCommGrp M (DerivedCategory.Q.obj (K.gradedPiece p)) (p + q))
  /-- Eventual target-filtration control makes the page-one presentation bounded. -/
  bounded : VanishesAbove M K → StabilizesBelow M K →
    CohomologicalSpectralSequence.IsBoundedFromZero E
  /-- Eventual target-filtration control makes the spectral sequence converge to the displayed
  abutment. -/
  converges : VanishesAbove M K → StabilizesBelow M K →
    FilteredComplex.Cohomology.Convergence.Converges F E

/-- Remark 19.13.8: every filtered target complex yields an associated Ext spectral sequence
with the expected first page and abutment, bounded and convergent under the canonical eventual
vanishing and stabilization hypotheses. -/
@[stacks 0G1X]
theorem existsSpectralSequence [IsGrothendieckAbelian.{w} A]
    (M : DerivedCategory A) (K : FilteredComplex A) :
    ∃ (F : FilteredComplex AddCommGrpCat.{t})
      (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0),
      IsSpectralSequence M K F E := sorry

end Target

namespace Source

/-- Eventual vanishing of `Ext⁽n⁾(M / F^p M, K)` as the source filtration index tends to
`-∞`. -/
@[stacks 0G1Z "source-filtration vanishing"]
def VanishesBelow (M : FilteredComplex A) (K : DerivedCategory A) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ →
    IsZero (addCommGrp (DerivedCategory.Q.obj (M.quotient p)) K n)

/-- Eventual stabilization of the canonical maps
`Ext⁽n⁾(M / F^p M, K) ⟶ Ext⁽n⁾(M, K)` as the source filtration index tends to `+∞`. -/
@[stacks 0G1Z "source-filtration stabilization"]
def StabilizesAbove (M : FilteredComplex A) (K : DerivedCategory A) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
    IsIso (ShiftedHom.precomp (DerivedCategory.Q.map (M.underlyingToQuotient p)) K n)

/-- A genuine filtered-complex model for the source-filtered Ext spectral sequence. -/
@[stacks 0G1Z "source-filtered Ext spectral sequence"]
structure IsSpectralSequence (M : FilteredComplex A) (K : DerivedCategory A)
    (F : FilteredComplex AddCommGrpCat.{t})
    (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0) : Prop
    extends FilteredComplex.SpectralSequence.Realizes F E
      (fun n => addCommGrp (DerivedCategory.Q.obj M.underlying) K n) where
  /-- The first page is `Ext⁽p+q⁾(gr^{-p} M, K)`. -/
  pageOne : ∀ p q : ℤ,
    Nonempty ((E.page 1).X (p, q) ≅
      addCommGrp (DerivedCategory.Q.obj (M.gradedPiece (-p))) K (p + q))
  /-- Eventual source-filtration control makes the page-one presentation bounded. -/
  bounded : VanishesBelow M K → StabilizesAbove M K →
    CohomologicalSpectralSequence.IsBoundedFromZero E
  /-- Eventual source-filtration control makes the spectral sequence converge to the displayed
  abutment. -/
  converges : VanishesBelow M K → StabilizesAbove M K →
    FilteredComplex.Cohomology.Convergence.Converges F E

/-- Remark 19.13.10: every filtered source complex yields an associated Ext spectral sequence
with the expected first page and abutment, bounded and convergent under the canonical eventual
vanishing and stabilization hypotheses. -/
@[stacks 0G1Z]
theorem existsSpectralSequence [IsGrothendieckAbelian.{w} A]
    (M : FilteredComplex A) (K : DerivedCategory A) :
    ∃ (F : FilteredComplex AddCommGrpCat.{t})
      (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0),
      IsSpectralSequence M K F E := sorry

end Source

end Derived

end CategoryTheory.DerivedCategory.Ext
