/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complete
public import ReasLib.CategoryTheory.Filtration.Complex.Cohomology
public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import ReasLib.CategoryTheory.Filtration.Complex.Representatives
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded
public import ReasLib.CategoryTheory.Homology.SpectralSequence.LimitStages
public import ReasLib.CategoryTheory.Filtration.Morphism.LimitRepresentatives

/-!
# Convergence of Spectral Sequences of Filtered Complexes

@stack 012U
@stack 012W

Convergence is first defined relative to explicit eventual cycle and boundary representatives
`Z_∞`, `B_∞` of the filtered complex (Stacks 012Q).  Weak convergence (Stacks 012U) asks that the
identification of `gr^p H^n` as a subquotient of `E_∞^{p,n-p}` be an equality; following
Stacks 012V this is expressed by equality of the eventual and intrinsic representatives, not by
an abstract isomorphism of objects.  This reusable core does not require every subobject lattice
in the ambient category to be complete.  The unqualified predicates record the existence of the
eventual representatives.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace FilteredComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Cohomology.Convergence

/-- Explicit eventual boundary and cycle representatives of a filtered complex in every degree.
In degree `n`, the boundary representatives are those of the incoming differential
`K^{n-1} → K^n` and the cycle representatives are those of the outgoing differential
`K^n → K^{n+1}`; both are subobjects of `K^n`.  These are the objects `B_∞` and `Z_∞` whose
existence is assumed in Stacks 012Q.  By `FilteredObject.Hom.LimitRepresentatives.eq` such a
package is unique when it exists. -/
@[stacks 012Q "explicit eventual cycle and boundary representatives of a filtered complex"]
structure LimitRepresentatives (K : FilteredComplex C) where
  /-- The eventual boundary representatives of the differential entering degree `n`. -/
  boundary : ∀ n : ℤ, FilteredObject.Hom.LimitRepresentatives (K.d (n - 1) n)
  /-- The eventual cycle representatives of the differential leaving degree `n`. -/
  cycle : ∀ n : ℤ, FilteredObject.Hom.LimitRepresentatives (K.d n (n + 1))

/-- Relative to explicit eventual representatives `R`, weak convergence means that `E` is
associated to `K` and that the identification of `gr^p H^n(K)` with a subquotient of
`E_∞^{p,n-p}` from Stacks 012Q is an equality: the inclusions (012T) of eventual boundaries in
intrinsic boundaries and (012S) of intrinsic cycles in eventual cycles are equalities in every
degree `n` and filtration index `p`. -/
@[stacks 012U "weak convergence relative to explicit eventual representatives"]
def IsWeakAlong
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)
    (R : LimitRepresentatives K) : Prop :=
  FilteredComplex.IsAssociated K E ∧
    ∀ n p : ℤ,
      (R.boundary n).boundary p = Cohomology.Representative.boundary K n p ∧
        Cohomology.Representative.cycle K n p = (R.cycle n).cycle p

namespace IsWeakAlong

variable {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
  {R : LimitRepresentatives K}

/-- Weak convergence along `R` includes the assertion that the spectral sequence is associated
to the filtered complex. -/
@[stacks 012U "associated spectral sequence from weak convergence"]
theorem isAssociated (h : IsWeakAlong K E R) : FilteredComplex.IsAssociated K E := sorry

/-- Weak convergence along `R` makes the eventual boundary representative equal to the
intrinsic boundary representative. -/
@[stacks 012V "eventual boundary equality from weak convergence"]
theorem boundary_eq (h : IsWeakAlong K E R) (n p : ℤ) :
    (R.boundary n).boundary p = Cohomology.Representative.boundary K n p := sorry

/-- Weak convergence along `R` makes the intrinsic cycle representative equal to the eventual
cycle representative. -/
@[stacks 012V "eventual cycle equality from weak convergence"]
theorem cycle_eq (h : IsWeakAlong K E R) (n p : ℤ) :
    Cohomology.Representative.cycle K n p = (R.cycle n).cycle p := sorry

/-- Assemble weak convergence along `R` from association and the boundary and cycle
equalities. -/
@[stacks 012V "weak convergence from representative equalities"]
theorem of_equalities (hAssoc : FilteredComplex.IsAssociated K E)
    (hB : ∀ n p : ℤ,
      (R.boundary n).boundary p = Cohomology.Representative.boundary K n p)
    (hZ : ∀ n p : ℤ,
      Cohomology.Representative.cycle K n p = (R.cycle n).cycle p) :
    IsWeakAlong K E R := sorry

/-- Under weak convergence, every graded piece of cohomology is isomorphic to the corresponding
infinity-page entry computed from any explicit limit stages of the spectral sequence. -/
@[stacks 012U "weak convergence graded-piece comparison"]
theorem isIsomorphic (h : IsWeakAlong K E R)
    (L : SpectralSequence.LimitStages (CohomologicalSpectralSequence.Page.One.ofZero E))
    (n p : ℤ) :
    IsIsomorphic ((K.inducedCohomologyFiltration n).gradedPiece p)
      (L.infinityPage (p, n - p)) := sorry

end IsWeakAlong

/-- A spectral sequence weakly converges to filtered-complex cohomology when it is associated to
the filtered complex, the eventual representatives `Z_∞` and `B_∞` exist in every degree, and
they agree with the intrinsic cycle and boundary representatives. -/
@[stacks 012U "weak convergence to filtered-complex cohomology"]
def IsWeak
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0) : Prop :=
  ∃ R : LimitRepresentatives K, IsWeakAlong K E R

namespace IsWeak

/-- Weak convergence relative to specified eventual representatives supplies the unqualified existence
predicate. -/
theorem of_along
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    {R : LimitRepresentatives K}
    (hR : IsWeakAlong K E R) : IsWeak K E := sorry

/-- Weak convergence supplies explicit eventual representatives along which the representative equalities
hold. -/
theorem exists_along
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (h : IsWeak K E) :
    ∃ R : LimitRepresentatives K, IsWeakAlong K E R := sorry

/-- A weakly convergent spectral sequence is associated to the filtered complex. -/
@[stacks 012U "associated spectral sequence from weak convergence"]
theorem isAssociated
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (h : IsWeak K E) : FilteredComplex.IsAssociated K E := sorry

end IsWeak

/-- Relative to explicit eventual representatives, abutment is weak convergence together with separated and
exhaustive cohomology filtrations. -/
@[stacks 012U "abutment relative to explicit eventual representatives"]
def AbutsAlong
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)
    (R : LimitRepresentatives K) : Prop :=
  IsWeakAlong K E R ∧
    Cohomology.Filtration.IsSeparatedExhaustive K

namespace AbutsAlong

variable {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
  {R : LimitRepresentatives K}

/-- Abutment along specified eventual representatives supplies weak convergence along those same representatives. -/
theorem isWeak (h : AbutsAlong K E R) : IsWeakAlong K E R := sorry

/-- Abutment along specified eventual representatives supplies separatedness and exhaustiveness of the
induced cohomology filtrations. -/
theorem isSeparatedExhaustive (h : AbutsAlong K E R) :
    Cohomology.Filtration.IsSeparatedExhaustive K := sorry

/-- Assemble abutment along specified eventual representatives from weak convergence along those representatives and
the intrinsic filtration condition. -/
theorem of_isWeak
    (hweak : IsWeakAlong K E R)
    (hfiltration : Cohomology.Filtration.IsSeparatedExhaustive K) :
    AbutsAlong K E R := sorry

end AbutsAlong

/-- A spectral sequence abuts to cohomology when it weakly converges and the induced cohomology
filtrations are separated and exhaustive.  The existential choice of eventual representatives is owned once
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

/-- Abutment relative to specified eventual representatives supplies the unqualified abutment predicate. -/
theorem of_along
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    {R : LimitRepresentatives K}
    (hR : AbutsAlong K E R) : Abuts K E := sorry

/-- Abutment supplies explicit eventual representatives along which weak convergence holds. -/
@[stacks 012U "explicit eventual representatives from abutment"]
theorem exists_along
    (h : Abuts K E) :
    ∃ R : LimitRepresentatives K, AbutsAlong K E R := sorry

end Abuts

/-- Relative to explicit eventual representatives, convergence consists of regularity, abutment, and
completeness of the induced cohomology filtrations. -/
@[stacks 012U "convergence relative to explicit eventual representatives"]
def ConvergesAlong
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0)
    (R : LimitRepresentatives K) : Prop :=
  E.IsRegular ∧ AbutsAlong K E R ∧ Cohomology.Filtration.IsComplete K

namespace ConvergesAlong

variable {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
  {R : LimitRepresentatives K}

/-- Convergence along specified eventual representatives supplies regularity of the spectral sequence. -/
theorem isRegular (h : ConvergesAlong K E R) : E.IsRegular := sorry

/-- Convergence along specified eventual representatives supplies abutment along those same representatives. -/
theorem abuts (h : ConvergesAlong K E R) : AbutsAlong K E R := sorry

/-- Convergence along specified eventual representatives supplies completeness of the induced cohomology
filtrations. -/
theorem isComplete (h : ConvergesAlong K E R) :
    Cohomology.Filtration.IsComplete K := sorry

/-- Assemble convergence along specified eventual representatives from regularity, abutment along those
representatives, and completeness. -/
theorem of_abuts
    (hregular : E.IsRegular) (habuts : AbutsAlong K E R)
    (hcomplete : Cohomology.Filtration.IsComplete K) :
    ConvergesAlong K E R := sorry

end ConvergesAlong

/-- A spectral sequence converges to filtered-complex cohomology when it is regular, abuts, and
the induced cohomology filtrations are complete.  Only the weak-convergence component of
`Abuts` retains an existential choice of eventual representatives. -/
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

/-- Convergence relative to specified eventual representatives supplies the unqualified convergence predicate. -/
theorem of_along
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    {R : LimitRepresentatives K}
    (hR : ConvergesAlong K E R) : Converges K E := sorry

/-- Convergence supplies explicit eventual representatives along which all its convergence conditions hold. -/
@[stacks 012U "explicit eventual representatives from convergence"]
theorem exists_along
    (h : Converges K E) :
    ∃ R : LimitRepresentatives K, ConvergesAlong K E R := sorry

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

/-- For an associated spectral sequence of a complex with finite term filtrations, the eventual
representatives stabilize at the intrinsic cycles and boundaries, so weak convergence holds along
any explicit eventual representatives. -/
theorem Convergence.isWeakAlong (hfinite : K.HasFiniteFiltrations)
    (hAssoc : FilteredComplex.IsAssociated K E)
    (R : FilteredComplex.Cohomology.Convergence.LimitRepresentatives K) :
    FilteredComplex.Cohomology.Convergence.IsWeakAlong K E R := sorry

/-- Finite term filtrations provide eventual representatives along which the associated spectral
sequence weakly converges. -/
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
