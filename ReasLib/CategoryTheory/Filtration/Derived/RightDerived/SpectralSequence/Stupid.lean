/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Stupid
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence

/-!
# Stupid-filtration spectral sequences for unbounded right-derived functors

The stupid filtration of a cochain complex produces the first hypercohomology spectral sequence.
This file records the construction for an arbitrary unbounded right-derived functor; geometric
global-sections statements are thin specializations of this owner.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- A stupid-filtration realization of a right-derived spectral sequence.  The original generic
realization retains the filtered resolution and association data, while `pageOneIso` records the
source-facing formula `E₁^{p,q} = R^q F(K^p)`. -/
@[stacks 0FLK "stupid-filtration right-derived spectral sequence"]
structure Realization (K : CochainComplex A ℤ) where
  /-- The right-derived realization of the stupid filtration. -/
  original : RightDerived.SpectralSequence.Realization F K.stupidFiltration
  /-- The `p`-th graded piece is the term `K^p` placed in degree `p`. -/
  gradedPieceIso : ∀ p : ℤ,
    K.stupidFiltration.gradedPiece p ≅ (CochainComplex.singleFunctor A p).obj (K.X p)
  /-- The first page is the right-derived cohomology of each term of the source complex. -/
  pageOneIso : ∀ (p : ℤ) (q : ℕ),
    (original.sequence.page 1).X (p, Int.ofNat q) ≅ (F.rightDerived q).obj (K.X p)
  /-- The first-page differential agrees with the derived image of the source differential. -/
  pageOneCommSq : ∀ (p : ℤ) (q : ℕ),
    CommSq
      ((original.sequence.page 1).d (p, Int.ofNat q) (p + 1, Int.ofNat q))
      (pageOneIso p q).hom
      (pageOneIso (p + 1) q).hom
      ((F.rightDerived q).map (K.d p (p + 1)))
  /-- The first page vanishes in negative cohomological rows. -/
  pageOneIsZero : ∀ (p q : ℤ), q < 0 →
    IsZero ((original.sequence.page 1).X (p, q))
  /-- The filtered model abuts to the cohomology of the total right-derived value of `K`. -/
  targetIso : ∀ n : ℤ,
    original.filtered.underlying.homology n ≅
      Functor.RightDerived.Homotopy.cochainCohomology F K n

namespace Realization

/-- The filtered model of a stupid-filtration realization. -/
@[stacks 0FLK "filtered model of a stupid-filtration realization"]
noncomputable abbrev filtered {K : CochainComplex A ℤ} (S : Realization F K) :
    FilteredComplex B :=
  S.original.filtered

/-- The associated cohomological spectral sequence. -/
@[stacks 0FLK "sequence of a stupid-filtration realization"]
noncomputable abbrev sequence {K : CochainComplex A ℤ} (S : Realization F K) :
    CohomologicalSpectralSequence B 0 :=
  S.original.sequence

/-- The selected sequence is associated to the filtered right-derived model. -/
@[stacks 0FLK "association of a stupid-filtration realization"]
theorem isAssociated {K : CochainComplex A ℤ} (S : Realization F K) :
    FilteredComplex.IsAssociated S.filtered S.sequence := sorry

/-- Every cochain complex admits a stupid-filtration right-derived realization. -/
@[stacks 0FLK]
theorem nonempty [IsGrothendieckAbelian.{w} A] (K : CochainComplex A ℤ) :
    Nonempty (Realization F K) := sorry

/-- A bounded-below complex gives a bounded stupid-filtration spectral sequence. -/
@[stacks 0FLK "boundedness of a stupid-filtration realization"]
theorem isBounded (K : CochainComplex.Plus A) (S : Realization F K.obj) :
    S.sequence.IsBounded := sorry

/-- A bounded-below complex gives finite filtrations on the abutment cohomology. -/
@[stacks 0FLK "finite filtration of a stupid-filtration realization"]
theorem finite (K : CochainComplex.Plus A) (S : Realization F K.obj) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.filtered := sorry

/-- A bounded-below complex gives convergence of its stupid-filtration spectral sequence. -/
@[stacks 0FLK "convergence of a stupid-filtration realization"]
theorem converges (K : CochainComplex.Plus A) (S : Realization F K.obj) :
    FilteredComplex.Cohomology.Convergence.Converges S.filtered S.sequence := sorry

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid
