/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Filtered
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Renumbering
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded.FromZero

/-!
# Source Hyper-Ext Spectral Sequences

Source-side specializations of filtered extension spectral sequences to truncation and stupid
filtrations, including their canonical page-and-bidegree renumbering.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated ShiftedHom
open scoped DerivedExt

noncomputable section

universe t w v u

namespace CategoryTheory.DerivedCategory.Ext.Source

section Derived

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{t} A]

namespace Truncation

/-- The first-page form of the hyper-Ext spectral sequence obtained from the canonical
truncation filtration of the source. -/
@[stacks 0G20 "source truncation spectral sequence"]
structure IsSpectralSequence (M K : DerivedCategory A)
    (F : FilteredComplex AddCommGrpCat.{t})
    (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0) : Prop
    extends FilteredComplex.SpectralSequence.Realizes F E
      (fun n => addCommGrp M K n) where
  /-- Before renumbering, `E₁^{p,q} = Ext⁽2p+q⁾(H^p(M), K)`. -/
  pageOne : ∀ p q : ℤ,
    Nonempty ((E.page 1).X (p, q) ≅
      addCommGrp (cohomologyObject M p) K (2 * p + q))
  /-- The standard `D^-`/`D^+` hypotheses make the page-one presentation bounded. -/
  bounded : IsBoundedAbove M → IsBoundedBelow K →
    CohomologicalSpectralSequence.IsBoundedFromZero E
  /-- The standard `D^-`/`D^+` hypotheses imply convergence to Ext. -/
  converges : IsBoundedAbove M → IsBoundedBelow K →
    FilteredComplex.Cohomology.Convergence.Converges F E

/-- Remark 19.13.11 (1): the canonical source truncation filtration gives the unrenumbered
first-page hyper-Ext spectral sequence. -/
@[stacks 0G20 "source truncation filtration"]
theorem existsSpectralSequence [IsGrothendieckAbelian.{w} A]
    (M K : DerivedCategory A) :
    ∃ (F : FilteredComplex AddCommGrpCat.{t})
      (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0),
      IsSpectralSequence M K F E := sorry

end Truncation

namespace Cohomology

/-- The representation-independent, renumbered hyper-Ext spectral sequence whose second page
is expressed using the cohomology objects of the source.  The old and new spectral sequences
are related by the canonical simultaneous page and bidegree renumbering. -/
@[stacks 0G20 "source cohomology spectral sequence"]
structure IsSpectralSequence (M K : DerivedCategory A)
    (F : FilteredComplex AddCommGrpCat.{t})
    (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0)
    (E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}) : Prop where
  /-- The unrenumbered sequence is the source truncation-filtration Ext spectral sequence. -/
  truncation : Truncation.IsSpectralSequence M K F E
  /-- The new sequence is the page-and-bidegree renumbering of the old sequence beginning at
  its first page. -/
  renumbering : CohomologicalSpectralSequence.Renumber.IsFromZero E E'

namespace IsSpectralSequence

/-- The source cohomology model realizes its Ext abutment while retaining the original spectral
sequence and its renumbering relation. -/
@[stacks 0G20 "renumbered source realization"]
theorem realizesViaRenumbering {M K : DerivedCategory A}
    {F : FilteredComplex AddCommGrpCat.{t}}
    {E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0}
    {E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}}
    (h : IsSpectralSequence M K F E E') :
    FilteredComplex.SpectralSequence.RealizesViaRenumbering F E E'
      (fun n => addCommGrp M K n) := sorry

/-- The standard `D^-`/`D^+` hypotheses imply boundedness of the renumbered source sequence. -/
@[stacks 0G20 "renumbered source boundedness"]
theorem bounded {M K : DerivedCategory A}
    {F : FilteredComplex AddCommGrpCat.{t}}
    {E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0}
    {E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}}
    (h : IsSpectralSequence M K F E E')
    (hM : IsBoundedAbove M) (hK : IsBoundedBelow K) :
    E'.IsBounded := sorry

/-- Under the standard boundedness hypotheses, the retained original source sequence converges
and renumbers to the displayed `E₂`-sequence. -/
@[stacks 0G20 "indexed renumbered source convergence"]
theorem convergesViaRenumbering {M K : DerivedCategory A}
    {F : FilteredComplex AddCommGrpCat.{t}}
    {E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0}
    {E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}}
    (h : IsSpectralSequence M K F E E')
    (hM : IsBoundedAbove M) (hK : IsBoundedBelow K) :
    FilteredComplex.Cohomology.Convergence.ConvergesViaRenumbering F E E' := sorry

/-- Under the standard boundedness hypotheses, the renumbered source spectral sequence
converges through its truncation-filtration presentation. -/
@[stacks 0G20 "renumbered source convergence"]
theorem convergesAfterRenumbering {M K : DerivedCategory A}
    {F : FilteredComplex AddCommGrpCat.{t}}
    {E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0}
    {E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}}
    (h : IsSpectralSequence M K F E E')
    (hM : IsBoundedAbove M) (hK : IsBoundedBelow K) :
    FilteredComplex.Cohomology.Convergence.ConvergesAfterRenumbering F E' := sorry

/-- The second page of a source truncation renumbering is
`E₂^{i,j} = Ext⁽i⁾(H^{-j}(M), K)`. -/
@[stacks 0G20 "renumbered source second page"]
theorem pageTwo {M K : DerivedCategory A}
    {F : FilteredComplex AddCommGrpCat.{t}}
    {E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0}
    {E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}}
    (h : IsSpectralSequence M K F E E') (i j : ℤ) :
    Nonempty ((E'.page 2).X (i, j) ≅ addCommGrp (cohomologyObject M (-j)) K i) := sorry

end IsSpectralSequence

/-- Remark 19.13.11 (2): the renumbered source hyper-Ext spectral sequence depends only on the
two derived objects and has second page `Ext⁽i⁾(H^{-j}(M), K)`. -/
@[stacks 0G20 "renumbered source cohomology spectral sequence"]
theorem existsSpectralSequence [IsGrothendieckAbelian.{w} A]
    (M K : DerivedCategory A) :
    ∃ (F : FilteredComplex AddCommGrpCat.{t})
      (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0)
      (E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}),
      IsSpectralSequence M K F E E' := sorry

end Cohomology

namespace Stupid

/-- The Ext spectral sequence attached to the stupid filtration of a source cochain complex. -/
@[stacks 0G20 "source stupid-filtration spectral sequence"]
structure IsSpectralSequence (M : CochainComplex A ℤ) (K : DerivedCategory A)
    (F : FilteredComplex AddCommGrpCat.{t})
    (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0) : Prop
    extends FilteredComplex.SpectralSequence.Realizes F E
      (fun n => addCommGrp (DerivedCategory.Q.obj M) K n) where
  /-- The first page is `E₁^{p,q} = Ext⁽q⁾(M^{-p}, K)`. -/
  pageOne : ∀ p q : ℤ,
    Nonempty ((E.page 1).X (p, q) ≅ addCommGrp (termObject M (-p)) K q)
  /-- Boundedness above of `M` and below of `K` make the page-one presentation bounded. -/
  bounded : (∃ n : ℤ, M.IsStrictlyLE n) → IsBoundedBelow K →
    CohomologicalSpectralSequence.IsBoundedFromZero E
  /-- The same hypotheses imply convergence to Ext. -/
  converges : (∃ n : ℤ, M.IsStrictlyLE n) → IsBoundedBelow K →
    FilteredComplex.Cohomology.Convergence.Converges F E

/-- Remark 19.13.11 (3): the stupid filtration of a bounded-above source complex produces the
first-page spectral sequence `E₁^{p,q} = Ext⁽q⁾(M^{-p}, K)`. -/
@[stacks 0G20 "source stupid filtration"]
theorem existsSpectralSequence [IsGrothendieckAbelian.{w} A]
    (M : CochainComplex A ℤ) (K : DerivedCategory A) :
    ∃ (F : FilteredComplex AddCommGrpCat.{t})
      (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0),
      IsSpectralSequence M K F E := sorry

end Stupid

end Derived

end CategoryTheory.DerivedCategory.Ext.Source
