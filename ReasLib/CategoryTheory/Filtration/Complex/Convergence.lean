module

public import ReasLib.CategoryTheory.Filtration.Complete
public import ReasLib.CategoryTheory.Filtration.Complex.Cohomology
public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded
public import ReasLib.CategoryTheory.Homology.SpectralSequence.LimitStages

/-!
# Convergence of Spectral Sequences of Filtered Complexes

@stack 012U
@stack 012W

Convergence is first defined relative to explicit limit-stage data.  This is the reusable core:
it does not require every subobject lattice in the ambient category to be complete.  The
corresponding unqualified predicates record the existence statement and remain convenient for
source-facing convergence theorems.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace FilteredComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Cohomology.Convergence

/-- Relative to explicit limit stages `L`, weak convergence means that `E` is associated to `K`
and identifies every graded piece of cohomology with the corresponding entry of the resulting
infinity page. -/
@[stacks 012U "weak convergence relative to explicit limit stages"]
def IsWeakAlong
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)
    (L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E)) : Prop :=
  FilteredComplex.IsAssociated K E ∧
    ∀ n p : ℤ,
      Nonempty
        ((K.inducedCohomologyFiltration n).gradedPiece p ≅
          L.infinityPage (p, n - p))

namespace IsWeakAlong

/-- Weak convergence along `L` includes the assertion that the spectral sequence is associated
to the filtered complex. -/
@[stacks 012U "associated spectral sequence from weak convergence"]
theorem isAssociated
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    {L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E)}
    (h : IsWeakAlong K E L) : FilteredComplex.IsAssociated K E := sorry

/-- Weak convergence along `L` identifies the indicated graded piece of cohomology with the
corresponding infinity-page entry. -/
@[stacks 012U "weak convergence graded-piece comparison"]
theorem isIsomorphic
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    {L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E)}
    (h : IsWeakAlong K E L) (n p : ℤ) :
    IsIsomorphic ((K.inducedCohomologyFiltration n).gradedPiece p)
      (L.infinityPage (p, n - p)) := sorry

end IsWeakAlong

/-- A spectral sequence weakly converges to filtered-complex cohomology when it is associated to
the filtered complex and admits explicit limit stages with the required graded-piece comparisons. -/
@[stacks 012U "weak convergence to filtered-complex cohomology"]
def IsWeak
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0) : Prop :=
  ∃ L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E),
    IsWeakAlong K E L

namespace IsWeak

/-- Weak convergence relative to specified limit stages supplies the unqualified existence
predicate. -/
theorem of_along
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    {L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E)}
    (hL : IsWeakAlong K E L) : IsWeak K E := sorry

/-- Weak convergence supplies explicit limit stages along which its graded-piece comparison
holds. -/
theorem exists_along
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (h : IsWeak K E) :
    ∃ L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E),
      IsWeakAlong K E L := sorry

/-- A weakly convergent spectral sequence is associated to the filtered complex. -/
@[stacks 012U "associated spectral sequence from weak convergence"]
theorem isAssociated
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (h : IsWeak K E) : FilteredComplex.IsAssociated K E := sorry

end IsWeak

/-- Relative to explicit limit stages, abutment is weak convergence together with separated and
exhaustive cohomology filtrations. -/
@[stacks 012U "abutment relative to explicit limit stages"]
def AbutsAlong
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)
    (L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E)) : Prop :=
  IsWeakAlong K E L ∧
    Cohomology.Filtration.IsSeparatedExhaustive K

namespace AbutsAlong

variable {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
  {L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E)}

/-- Abutment along specified limit stages supplies weak convergence along those same stages. -/
theorem isWeak (h : AbutsAlong K E L) : IsWeakAlong K E L := sorry

/-- Abutment along specified limit stages supplies separatedness and exhaustiveness of the
induced cohomology filtrations. -/
theorem isSeparatedExhaustive (h : AbutsAlong K E L) :
    Cohomology.Filtration.IsSeparatedExhaustive K := sorry

/-- Assemble abutment along specified limit stages from weak convergence along those stages and
the intrinsic filtration condition. -/
theorem of_isWeak
    (hweak : IsWeakAlong K E L)
    (hfiltration : Cohomology.Filtration.IsSeparatedExhaustive K) :
    AbutsAlong K E L := sorry

end AbutsAlong

/-- A spectral sequence abuts to cohomology when it weakly converges and the induced cohomology
filtrations are separated and exhaustive.  The existential choice of limit stages is owned once
by `IsWeak`; the filtration condition is independent of that choice. -/
@[stacks 012U "abutment to filtered-complex cohomology"]
def Abuts
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0) : Prop :=
  IsWeak K E ∧ Cohomology.Filtration.IsSeparatedExhaustive K

namespace Abuts

variable {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}

/-- An abutment supplies weak convergence. -/
theorem isWeak (h : Abuts K E) : IsWeak K E := sorry

/-- An abutment supplies separatedness and exhaustiveness of the induced cohomology
filtrations. -/
theorem isSeparatedExhaustive (h : Abuts K E) :
    Cohomology.Filtration.IsSeparatedExhaustive K := sorry

/-- Assemble abutment from weak convergence and the intrinsic filtration condition. -/
theorem of_isWeak
    (hweak : IsWeak K E)
    (hfiltration : Cohomology.Filtration.IsSeparatedExhaustive K) :
    Abuts K E := sorry

/-- Abutment relative to specified limit stages supplies the unqualified abutment predicate. -/
theorem of_along
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    {L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E)}
    (hL : AbutsAlong K E L) : Abuts K E := sorry

/-- Abutment supplies explicit limit stages along which its weak-convergence comparison holds. -/
@[stacks 012U "explicit limit stages from abutment"]
theorem exists_along
    (h : Abuts K E) :
    ∃ L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E),
      AbutsAlong K E L := sorry

end Abuts

/-- Relative to explicit limit stages, convergence consists of regularity, abutment, and
completeness of the induced cohomology filtrations. -/
@[stacks 012U "convergence relative to explicit limit stages"]
def ConvergesAlong
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)
    (L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E)) : Prop :=
  E.IsRegular ∧ AbutsAlong K E L ∧ Cohomology.Filtration.IsComplete K

namespace ConvergesAlong

variable {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
  {L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E)}

/-- Convergence along specified limit stages supplies regularity of the spectral sequence. -/
theorem isRegular (h : ConvergesAlong K E L) : E.IsRegular := sorry

/-- Convergence along specified limit stages supplies abutment along those same stages. -/
theorem abuts (h : ConvergesAlong K E L) : AbutsAlong K E L := sorry

/-- Convergence along specified limit stages supplies completeness of the induced cohomology
filtrations. -/
theorem isComplete (h : ConvergesAlong K E L) :
    Cohomology.Filtration.IsComplete K := sorry

/-- Assemble convergence along specified limit stages from regularity, abutment along those
stages, and completeness. -/
theorem of_abuts
    (hregular : E.IsRegular) (habuts : AbutsAlong K E L)
    (hcomplete : Cohomology.Filtration.IsComplete K) :
    ConvergesAlong K E L := sorry

end ConvergesAlong

/-- A spectral sequence converges to filtered-complex cohomology when it is regular, abuts, and
the induced cohomology filtrations are complete.  Only the weak-convergence component of
`Abuts` retains an existential limit-stage choice. -/
@[stacks 012U]
def Converges
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0) : Prop :=
  E.IsRegular ∧ Abuts K E ∧ Cohomology.Filtration.IsComplete K

namespace Converges

variable {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}

/-- Convergence supplies regularity of the spectral sequence. -/
theorem isRegular (h : Converges K E) : E.IsRegular := sorry

/-- Convergence supplies abutment to filtered-complex cohomology. -/
theorem abuts (h : Converges K E) : Abuts K E := sorry

/-- Convergence supplies completeness of the induced cohomology filtrations. -/
theorem isComplete (h : Converges K E) : Cohomology.Filtration.IsComplete K := sorry

/-- Assemble convergence from regularity, abutment, and completeness. -/
theorem of_abuts
    (hregular : E.IsRegular) (habuts : Abuts K E)
    (hcomplete : Cohomology.Filtration.IsComplete K) :
    Converges K E := sorry

/-- Convergence relative to specified limit stages supplies the unqualified convergence predicate. -/
theorem of_along
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    {L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E)}
    (hL : ConvergesAlong K E L) : Converges K E := sorry

/-- Convergence supplies explicit limit stages along which all its convergence conditions hold. -/
@[stacks 012U "explicit limit stages from convergence"]
theorem exists_along
    (h : Converges K E) :
    ∃ L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E),
      ConvergesAlong K E L := sorry

end Converges

end Cohomology.Convergence

namespace HasFiniteFiltrations

variable {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}

/-- A finite filtration on every term makes any matching zeroth-page spectral sequence bounded. -/
@[stacks 012W "boundedness from finite term filtrations"]
theorem Convergence.isBounded (hfinite : K.HasFiniteFiltrations)
    (hpageZero : Page.Zero.IsGradedPiece K E) :
    E.IsBounded := sorry

/-- Finite term filtrations make an associated spectral sequence bounded. -/
@[stacks 012W "boundedness of an associated spectral sequence"]
theorem Convergence.isBounded_of_associated (hfinite : K.HasFiniteFiltrations)
    (hAssoc : FilteredComplex.IsAssociated K E) : E.IsBounded := sorry

/-- Finite filtrations on the terms induce finite filtrations on all cohomology objects. -/
@[stacks 012W "finiteness of the induced cohomology filtration"]
theorem Cohomology.isFinite (hfinite : K.HasFiniteFiltrations) :
    FilteredComplex.Cohomology.Filtration.IsFinite K := sorry

/-- Finite term filtrations make every induced cohomology filtration separated. -/
theorem Cohomology.isSeparated (hfinite : K.HasFiniteFiltrations) :
    ∀ n : ℤ, IndexedFiltration.IsSeparated (K.inducedCohomologyFiltration n) := sorry

/-- Finite term filtrations make every induced cohomology filtration exhaustive. -/
theorem Cohomology.isExhaustive (hfinite : K.HasFiniteFiltrations) :
    ∀ n : ℤ, IndexedFiltration.IsExhaustive (K.inducedCohomologyFiltration n) := sorry

/-- Finite term filtrations make every induced cohomology filtration separated and exhaustive. -/
theorem Cohomology.isSeparatedExhaustive (hfinite : K.HasFiniteFiltrations) :
    FilteredComplex.Cohomology.Filtration.IsSeparatedExhaustive K := sorry

/-- Finite term filtrations make every induced cohomology filtration complete. -/
theorem Cohomology.isComplete (hfinite : K.HasFiniteFiltrations) :
    FilteredComplex.Cohomology.Filtration.IsComplete K := sorry

/-- Associated page representatives and finite term filtrations identify cohomology graded
pieces with any explicit limit-stage model. -/
theorem Convergence.isWeakAlong (hfinite : K.HasFiniteFiltrations)
    (hAssoc : FilteredComplex.IsAssociated K E)
    (L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E)) :
    FilteredComplex.Cohomology.Convergence.IsWeakAlong K E L := sorry

/-- Finite term filtrations provide limit stages along which the associated spectral sequence
weakly converges. -/
theorem Convergence.isWeak (hfinite : K.HasFiniteFiltrations)
    (hAssoc : FilteredComplex.IsAssociated K E) :
    FilteredComplex.Cohomology.Convergence.IsWeak K E := sorry

/-- Finite term filtrations and weak convergence assemble into convergence to cohomology.
The zeroth-page comparison needed for boundedness is already part of weak convergence through
its association component. -/
theorem Convergence.converges_of_isWeak (hfinite : K.HasFiniteFiltrations)
    (hweak : FilteredComplex.Cohomology.Convergence.IsWeak K E) :
    FilteredComplex.Cohomology.Convergence.Converges K E := sorry

/-- An associated spectral sequence of a termwise finitely filtered complex converges to the
cohomology of the complex. -/
@[stacks 012W, stacks 0H7W "convergence from finite term filtrations"]
theorem Convergence.converges (hfinite : K.HasFiniteFiltrations)
    (hAssoc : FilteredComplex.IsAssociated K E) :
    FilteredComplex.Cohomology.Convergence.Converges K E := sorry

end HasFiniteFiltrations
end FilteredComplex
end CategoryTheory
