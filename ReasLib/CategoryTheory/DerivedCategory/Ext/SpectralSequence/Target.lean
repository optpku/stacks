module

public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Filtered
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Renumbering
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded.FromZero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Target Hyper-Ext Spectral Sequences

@stack 0G1Y
@stack 0AVH
@stack 0AVI

Target-side specializations of filtered extension spectral sequences to truncation and stupid
filtrations, including their canonical page-and-bidegree renumbering.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated ShiftedHom
open scoped DerivedExt

noncomputable section

universe t w v u

namespace CategoryTheory.DerivedCategory.Ext.Target

section Derived

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{t} A]

namespace Truncation

/-- The first-page form of the hyper-Ext spectral sequence obtained from the canonical
truncation filtration of the target. -/
@[stacks 0G1Y "target truncation spectral sequence"]
structure IsSpectralSequence (M K : DerivedCategory A)
    (F : FilteredComplex AddCommGrpCat.{t})
    (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0) : Prop
    extends FilteredComplex.SpectralSequence.Realizes F E
      (fun n => addCommGrp M K n) where
  /-- Before renumbering, `E₁^{p,q} = Ext⁽2p+q⁾(M, H^{-p}(K))`. -/
  pageOne : ∀ p q : ℤ,
    Nonempty ((E.page 1).X (p, q) ≅
      addCommGrp M (cohomologyObject K (-p)) (2 * p + q))
  /-- The standard `D^-`/`D^+` hypotheses make the page-one presentation bounded. -/
  bounded : IsBoundedAbove M → IsBoundedBelow K →
    CohomologicalSpectralSequence.IsBoundedFromZero E
  /-- The standard `D^-`/`D^+` hypotheses imply convergence to Ext. -/
  converges : IsBoundedAbove M → IsBoundedBelow K →
    FilteredComplex.Cohomology.Convergence.Converges F E

/-- Remark 19.13.9 (1): the canonical truncation filtration gives the unrenumbered first-page
hyper-Ext spectral sequence. -/
@[stacks 0G1Y "truncation filtration"]
theorem existsSpectralSequence [IsGrothendieckAbelian.{w} A]
    (M K : DerivedCategory A) :
    ∃ (F : FilteredComplex AddCommGrpCat.{t})
      (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0),
      IsSpectralSequence M K F E := sorry

end Truncation

namespace Cohomology

/-- The representation-independent, renumbered hyper-Ext spectral sequence whose second page
is expressed using the cohomology objects of the target.  The old and new spectral sequences
are related by the canonical simultaneous page and bidegree renumbering. -/
@[stacks 0G1Y, stacks 0AVH "target cohomology spectral sequence"]
structure IsSpectralSequence (M K : DerivedCategory A)
    (F : FilteredComplex AddCommGrpCat.{t})
    (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0)
    (E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}) : Prop where
  /-- The unrenumbered sequence is the truncation-filtration Ext spectral sequence. -/
  truncation : Truncation.IsSpectralSequence M K F E
  /-- The new sequence is the page-and-bidegree renumbering of the old sequence beginning at
  its first page. -/
  renumbering : CohomologicalSpectralSequence.Renumber.IsFromZero E E'

namespace IsSpectralSequence

/-- The target cohomology model realizes its Ext abutment while retaining the original spectral
sequence and its renumbering relation. -/
@[stacks 0G1Y, stacks 0AVH "renumbered target realization"]
theorem realizesViaRenumbering {M K : DerivedCategory A}
    {F : FilteredComplex AddCommGrpCat.{t}}
    {E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0}
    {E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}}
    (h : IsSpectralSequence M K F E E') :
    FilteredComplex.SpectralSequence.RealizesViaRenumbering F E E'
      (fun n => addCommGrp M K n) := sorry

/-- The standard `D^-`/`D^+` hypotheses imply boundedness of the renumbered target sequence. -/
@[stacks 0G1Y, stacks 0AVH "renumbered target boundedness"]
theorem bounded {M K : DerivedCategory A}
    {F : FilteredComplex AddCommGrpCat.{t}}
    {E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0}
    {E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}}
    (h : IsSpectralSequence M K F E E')
    (hM : IsBoundedAbove M) (hK : IsBoundedBelow K) :
    E'.IsBounded := sorry

/-- Under the standard boundedness hypotheses, the retained original target sequence converges
and renumbers to the displayed `E₂`-sequence. -/
@[stacks 0G1Y, stacks 0AVH "indexed renumbered target convergence"]
theorem convergesViaRenumbering {M K : DerivedCategory A}
    {F : FilteredComplex AddCommGrpCat.{t}}
    {E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0}
    {E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}}
    (h : IsSpectralSequence M K F E E')
    (hM : IsBoundedAbove M) (hK : IsBoundedBelow K) :
    FilteredComplex.Cohomology.Convergence.ConvergesViaRenumbering F E E' := sorry

/-- Under the standard boundedness hypotheses, the renumbered target spectral sequence
converges through its truncation-filtration presentation. -/
@[stacks 0G1Y, stacks 0AVH "renumbered target convergence"]
theorem convergesAfterRenumbering {M K : DerivedCategory A}
    {F : FilteredComplex AddCommGrpCat.{t}}
    {E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0}
    {E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}}
    (h : IsSpectralSequence M K F E E')
    (hM : IsBoundedAbove M) (hK : IsBoundedBelow K) :
    FilteredComplex.Cohomology.Convergence.ConvergesAfterRenumbering F E' := sorry

/-- The second page of a target truncation renumbering is
`E₂^{i,j} = Ext⁽i⁾(M, H^j(K))`. -/
@[stacks 0G1Y, stacks 0AVH "renumbered target second page"]
theorem pageTwo {M K : DerivedCategory A}
    {F : FilteredComplex AddCommGrpCat.{t}}
    {E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0}
    {E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}}
    (h : IsSpectralSequence M K F E E') (i j : ℤ) :
    Nonempty ((E'.page 2).X (i, j) ≅ addCommGrp M (cohomologyObject K j) i) := sorry

end IsSpectralSequence

/-- Remark 19.13.9 (2): the renumbered hyper-Ext spectral sequence depends only on the two
derived objects and has second page `Ext⁽i⁾(M, H^j(K))`. -/
@[stacks 0G1Y, stacks 0AVH "renumbered cohomology spectral sequence"]
theorem existsSpectralSequence [IsGrothendieckAbelian.{w} A]
    (M K : DerivedCategory A) :
    ∃ (F : FilteredComplex AddCommGrpCat.{t})
      (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0)
      (E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}),
      IsSpectralSequence M K F E E' := sorry

end Cohomology

namespace Stupid

/-- The Ext spectral sequence attached to the stupid filtration of a target cochain complex. -/
@[stacks 0G1Y, stacks 0AVI "target stupid-filtration spectral sequence"]
structure IsSpectralSequence (M : DerivedCategory A) (K : CochainComplex A ℤ)
    (F : FilteredComplex AddCommGrpCat.{t})
    (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0) : Prop
    extends FilteredComplex.SpectralSequence.Realizes F E
      (fun n => addCommGrp M (DerivedCategory.Q.obj K) n) where
  /-- The first page is `E₁^{p,q} = Ext⁽q⁾(M, K^p)`. -/
  pageOne : ∀ p q : ℤ,
    Nonempty ((E.page 1).X (p, q) ≅ addCommGrp M (termObject K p) q)
  /-- Boundedness above of `M` and below of `K` make the page-one presentation bounded. -/
  bounded : IsBoundedAbove M → (∃ n : ℤ, K.IsStrictlyGE n) →
    CohomologicalSpectralSequence.IsBoundedFromZero E
  /-- The same hypotheses imply convergence to Ext. -/
  converges : IsBoundedAbove M → (∃ n : ℤ, K.IsStrictlyGE n) →
    FilteredComplex.Cohomology.Convergence.Converges F E

/-- Remark 19.13.9 (3): the stupid filtration of a bounded-below target complex produces the
first-page spectral sequence `E₁^{p,q} = Ext⁽q⁾(M, K^p)`. -/
@[stacks 0G1Y, stacks 0AVI "stupid filtration"]
theorem existsSpectralSequence [IsGrothendieckAbelian.{w} A]
    (M : DerivedCategory A) (K : CochainComplex A ℤ) :
    ∃ (F : FilteredComplex AddCommGrpCat.{t})
      (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0),
      IsSpectralSequence M K F E := sorry

end Stupid

end Derived

end CategoryTheory.DerivedCategory.Ext.Target
