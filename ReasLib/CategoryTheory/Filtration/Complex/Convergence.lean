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
public import Mathlib.Data.Int.Interval

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
theorem isAssociated (h : IsWeakAlong K E R) : FilteredComplex.IsAssociated K E :=
  h.1

/-- Weak convergence along `R` makes the eventual boundary representative equal to the
intrinsic boundary representative. -/
@[stacks 012V "eventual boundary equality from weak convergence"]
theorem boundary_eq (h : IsWeakAlong K E R) (n p : ℤ) :
    (R.boundary n).boundary p = Cohomology.Representative.boundary K n p :=
  (h.2 n p).1

/-- Weak convergence along `R` makes the intrinsic cycle representative equal to the eventual
cycle representative. -/
@[stacks 012V "eventual cycle equality from weak convergence"]
theorem cycle_eq (h : IsWeakAlong K E R) (n p : ℤ) :
    Cohomology.Representative.cycle K n p = (R.cycle n).cycle p :=
  (h.2 n p).2

/-- Assemble weak convergence along `R` from association and the boundary and cycle
equalities. -/
@[stacks 012V "weak convergence from representative equalities"]
theorem of_equalities (hAssoc : FilteredComplex.IsAssociated K E)
    (hB : ∀ n p : ℤ,
      (R.boundary n).boundary p = Cohomology.Representative.boundary K n p)
    (hZ : ∀ n p : ℤ,
      Cohomology.Representative.cycle K n p = (R.cycle n).cycle p) :
    IsWeakAlong K E R :=
  ⟨hAssoc, fun n p ↦ ⟨hB n p, hZ n p⟩⟩

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
    (hR : IsWeakAlong K E R) : IsWeak K E :=
  ⟨R, hR⟩

/-- Weak convergence supplies explicit eventual representatives along which the representative equalities
hold. -/
theorem exists_along
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (h : IsWeak K E) :
    ∃ R : LimitRepresentatives K, IsWeakAlong K E R :=
  h

/-- A weakly convergent spectral sequence is associated to the filtered complex. -/
@[stacks 012U "associated spectral sequence from weak convergence"]
theorem isAssociated
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (h : IsWeak K E) : FilteredComplex.IsAssociated K E := by
  obtain ⟨R, hR⟩ := h
  exact hR.isAssociated

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
theorem isWeak (h : AbutsAlong K E R) : IsWeakAlong K E R :=
  h.1

/-- Abutment along specified eventual representatives supplies separatedness and exhaustiveness of the
induced cohomology filtrations. -/
theorem isSeparatedExhaustive (h : AbutsAlong K E R) :
    Cohomology.Filtration.IsSeparatedExhaustive K :=
  h.2

/-- Assemble abutment along specified eventual representatives from weak convergence along those representatives and
the intrinsic filtration condition. -/
theorem of_isWeak
    (hweak : IsWeakAlong K E R)
    (hfiltration : Cohomology.Filtration.IsSeparatedExhaustive K) :
    AbutsAlong K E R :=
  ⟨hweak, hfiltration⟩

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
theorem isWeak (h : Abuts K E) : IsWeak K E :=
  h.1

/-- An abutment supplies separatedness and exhaustiveness of the induced cohomology
filtrations. -/
theorem isSeparatedExhaustive (h : Abuts K E) :
    Cohomology.Filtration.IsSeparatedExhaustive K :=
  h.2

/-- Assemble abutment from weak convergence and the intrinsic filtration condition. -/
theorem of_isWeak
    (hweak : IsWeak K E)
    (hfiltration : Cohomology.Filtration.IsSeparatedExhaustive K) :
    Abuts K E :=
  ⟨hweak, hfiltration⟩

/-- Abutment relative to specified eventual representatives supplies the unqualified abutment predicate. -/
theorem of_along
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    {R : LimitRepresentatives K}
    (hR : AbutsAlong K E R) : Abuts K E :=
  ⟨IsWeak.of_along hR.1, hR.2⟩

/-- Abutment supplies explicit eventual representatives along which weak convergence holds. -/
@[stacks 012U "explicit eventual representatives from abutment"]
theorem exists_along
    (h : Abuts K E) :
    ∃ R : LimitRepresentatives K, AbutsAlong K E R := by
  obtain ⟨R, hR⟩ := h.1
  exact ⟨R, hR, h.2⟩

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
theorem isRegular (h : ConvergesAlong K E R) : E.IsRegular :=
  h.1

/-- Convergence along specified eventual representatives supplies abutment along those same representatives. -/
theorem abuts (h : ConvergesAlong K E R) : AbutsAlong K E R :=
  h.2.1

/-- Convergence along specified eventual representatives supplies completeness of the induced cohomology
filtrations. -/
theorem isComplete (h : ConvergesAlong K E R) :
    Cohomology.Filtration.IsComplete K :=
  h.2.2

/-- Assemble convergence along specified eventual representatives from regularity, abutment along those
representatives, and completeness. -/
theorem of_abuts
    (hregular : E.IsRegular) (habuts : AbutsAlong K E R)
    (hcomplete : Cohomology.Filtration.IsComplete K) :
    ConvergesAlong K E R :=
  ⟨hregular, habuts, hcomplete⟩

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
theorem isRegular (h : Converges K E) : E.IsRegular :=
  h.1

/-- Convergence supplies abutment to filtered-complex cohomology. -/
theorem abuts (h : Converges K E) : Abuts K E :=
  h.2.1

/-- Convergence supplies completeness of the induced cohomology filtrations. -/
theorem isComplete (h : Converges K E) : Cohomology.Filtration.IsComplete K :=
  h.2.2

/-- Assemble convergence from regularity, abutment, and completeness. -/
theorem of_abuts
    (hregular : E.IsRegular) (habuts : Abuts K E)
    (hcomplete : Cohomology.Filtration.IsComplete K) :
    Converges K E :=
  ⟨hregular, habuts, hcomplete⟩

/-- Convergence relative to specified eventual representatives supplies the unqualified convergence predicate. -/
theorem of_along
    {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    {R : LimitRepresentatives K}
    (hR : ConvergesAlong K E R) : Converges K E :=
  ⟨hR.1, Abuts.of_along hR.2.1, hR.2.2⟩

/-- Convergence supplies explicit eventual representatives along which all its convergence conditions hold. -/
@[stacks 012U "explicit eventual representatives from convergence"]
theorem exists_along
    (h : Converges K E) :
    ∃ R : LimitRepresentatives K, ConvergesAlong K E R := by
  obtain ⟨R, hR⟩ := h.abuts.exists_along
  exact ⟨R, h.1, hR, h.2.2⟩

end Converges

end Cohomology.Convergence

namespace HasFiniteFiltrations

variable {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}

/-- A finite filtration on every term makes any matching zeroth-page spectral sequence bounded. -/
@[stacks 012W "boundedness from finite term filtrations"]
theorem Convergence.isBounded (hfinite : K.HasFiniteFiltrations)
    (hpageZero : Page.Zero.IsGradedPiece K E) :
    E.IsBounded := by
  obtain ⟨A⟩ := hpageZero
  intro n
  obtain ⟨a, b, ha, hb⟩ := hfinite n
  have htop (i : ℤ) (hi : i ≤ a) : (K.X n).filtration.stage i = ⊤ :=
    top_unique (ha ▸ (K.X n).filtration.antitone hi)
  have hbot (i : ℤ) (hi : b ≤ i) : (K.X n).filtration.stage i = ⊥ :=
    le_bot_iff.mp (((K.X n).filtration.antitone hi).trans hb.le)
  have hzero (p : ℤ)
      (h : (K.X n).filtration.stage (p + 1) = (K.X n).filtration.stage p) :
      IsZero ((E.page 0).X (p, n - p)) := by
    haveI : IsIso ((K.X n).filtration.succInclusion p) :=
      (Subobject.isoOfEq _ _ h).isIso_hom
    have hz : IsZero ((GradedPiece.Column.complex K p).X (n - p)) := by
      change IsZero ((K.X (p + (n - p))).gradedPiece p)
      rw [show p + (n - p) = n by omega]
      exact isZero_cokernel_of_epi ((K.X n).filtration.succInclusion p)
    exact hz.of_iso
      ((CohomologicalSpectralSequence.PageZeroColumn.xIso E p (n - p)).symm ≪≫
        HomologicalComplex.Hom.isoApp (A.columnIso p) (n - p))
  apply (Set.finite_Icc a b).subset
  intro p hp
  change ¬ IsZero ((E.page 0).X (p, n - p)) at hp
  constructor
  · change a ≤ p
    by_contra h
    exact hp (hzero p ((htop (p + 1) (by omega)).trans (htop p (by omega)).symm))
  · change p ≤ b
    by_contra h
    exact hp (hzero p ((hbot (p + 1) (by omega)).trans (hbot p (by omega)).symm))

/-- Finite term filtrations make an associated spectral sequence bounded. -/
@[stacks 012W "boundedness of an associated spectral sequence"]
theorem Convergence.isBounded_of_associated (hfinite : K.HasFiniteFiltrations)
    (hAssoc : FilteredComplex.IsAssociated K E) : E.IsBounded := by
  obtain ⟨A⟩ := hAssoc
  exact Convergence.isBounded hfinite ⟨A.toComparison⟩

/-- Finite filtrations on the terms induce finite filtrations on all cohomology objects. -/
@[stacks 012W "finiteness of the induced cohomology filtration"]
theorem Cohomology.isFinite (hfinite : K.HasFiniteFiltrations) :
    FilteredComplex.Cohomology.Filtration.IsFinite K := by
  intro n
  obtain ⟨a', b', ha', hb'⟩ := hfinite ((ComplexShape.up ℤ).prev n)
  obtain ⟨a, b, ha, hb⟩ := hfinite n
  refine ⟨min a' a, b, ?_, ?_⟩
  · change (K.inducedCohomologyFiltration n).stage (min a' a) = ⊤
    haveI : IsIso ((K.stageInclusion (min a' a)).f ((ComplexShape.up ℤ).prev n)) := by
      change IsIso ((K.X ((ComplexShape.up ℤ).prev n)).filtration.stage (min a' a)).arrow
      apply (Subobject.isIso_arrow_iff_eq_top _).2
      exact top_unique (ha' ▸ (K.X _).filtration.antitone (min_le_left a' a))
    haveI : IsIso ((K.stageInclusion (min a' a)).f n) := by
      change IsIso ((K.X n).filtration.stage (min a' a)).arrow
      apply (Subobject.isIso_arrow_iff_eq_top _).2
      exact top_unique (ha ▸ (K.X n).filtration.antitone (min_le_right a' a))
    haveI : Mono ((K.stageInclusion (min a' a)).f ((ComplexShape.up ℤ).next n)) := by
      change Mono ((K.X _).filtration.stage (min a' a)).arrow
      infer_instance
    haveI : IsIso (K.cohomologyMap (min a' a) n) :=
      ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' _
        (inferInstanceAs (Epi ((K.stageInclusion (min a' a)).f ((ComplexShape.up ℤ).prev n))))
        (inferInstanceAs (IsIso ((K.stageInclusion (min a' a)).f n)))
        (inferInstanceAs (Mono ((K.stageInclusion (min a' a)).f ((ComplexShape.up ℤ).next n))))
    change imageSubobject (K.cohomologyMap (min a' a) n) = ⊤
    rw [imageSubobject_mono, Subobject.mk_eq_top_of_isIso]
  · change (K.inducedCohomologyFiltration n).stage b = ⊥
    have hz : IsZero ((K.stage b).X n) := by
      change IsZero (((K.X n).filtration.stage b : Subobject _) : C)
      rw [hb]
      exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
    have hzH := ((K.stage b).exactAt_iff_isZero_homology n).mp
      (HomologicalComplex.ExactAt.of_isZero hz)
    change imageSubobject (K.cohomologyMap b n) = ⊥
    rw [hzH.eq_of_src (K.cohomologyMap b n) 0, imageSubobject_zero]

/-- Finite term filtrations make every induced cohomology filtration separated. -/
theorem Cohomology.isSeparated (hfinite : K.HasFiniteFiltrations) :
    ∀ n : ℤ, IndexedFiltration.IsSeparated (K.inducedCohomologyFiltration n) := by
  intro n Y hY
  obtain ⟨a, b, ha, hb⟩ := Cohomology.isFinite hfinite n
  exact hb ▸ hY b

/-- Finite term filtrations make every induced cohomology filtration exhaustive. -/
theorem Cohomology.isExhaustive (hfinite : K.HasFiniteFiltrations) :
    ∀ n : ℤ, IndexedFiltration.IsExhaustive (K.inducedCohomologyFiltration n) := by
  intro n Y hY
  obtain ⟨a, b, ha, hb⟩ := Cohomology.isFinite hfinite n
  exact ha ▸ hY a

/-- Finite term filtrations make every induced cohomology filtration separated and exhaustive. -/
theorem Cohomology.isSeparatedExhaustive (hfinite : K.HasFiniteFiltrations) :
    FilteredComplex.Cohomology.Filtration.IsSeparatedExhaustive K :=
  ⟨Cohomology.isSeparated hfinite, Cohomology.isExhaustive hfinite⟩

/-- Finite term filtrations make every induced cohomology filtration complete. -/
theorem Cohomology.isComplete (hfinite : K.HasFiniteFiltrations) :
    FilteredComplex.Cohomology.Filtration.IsComplete K := by
  intro n
  exact DecreasingFiltration.isComplete_of_isFinite
    (K.inducedCohomologyFiltration n) (Cohomology.isFinite hfinite n)

private theorem kernel_le_pullback {X Y : FilteredObject C} (f : X ⟶ Y)
    (Z : Subobject Y.obj) :
    kernelSubobject f.hom ≤ (Subobject.pullback f.hom).obj Z := by
  apply Subobject.le_of_factors
  rw [pullback_factors_iff, Subobject.factors_iff]
  exact ⟨0, zero_comp.trans (kernelSubobject_arrow_comp f.hom).symm⟩

private theorem pullback_bot_eq_kernel {X Y : FilteredObject C} (f : X ⟶ Y) :
    (Subobject.pullback f.hom).obj ⊥ = kernelSubobject f.hom := by
  apply le_antisymm
  · show (Subobject.pullback f.hom).obj ⊥ ≤ kernelSubobject f.hom
    apply le_kernelSubobject
    rw [← (Subobject.isPullback f.hom ⊥).w, Subobject.bot_arrow, comp_zero]
  · show kernelSubobject f.hom ≤ (Subobject.pullback f.hom).obj ⊥
    exact kernel_le_pullback f ⊥

private theorem boundary_isLUB_of_finite {X Y : FilteredObject C} (f : X ⟶ Y)
    (hX : X.IsFinite) (p : ℤ) :
    IsLUB (Set.range fun r : ℕ ↦ f.boundaryRepresentative r p)
      (f.imageRepresentative p) := by
  refine ⟨?_, ?_⟩
  · show f.imageRepresentative p ∈ upperBounds _
    rintro _ ⟨r, rfl⟩
    apply sup_le_sup_right
    exact le_inf (inf_le_right.trans (imageSubobject_comp_le _ _)) inf_le_left
  · change ∀ Z ∈ upperBounds _, f.imageRepresentative p ≤ Z
    intro Z hZ
    obtain ⟨a, _, ha, _⟩ := hX
    let r : ℕ := (p + 1 - a).toNat
    have htop : X.filtration.stage (p - r + 1) = ⊤ :=
      top_unique (ha ▸ X.filtration.antitone (by dsimp [r]; omega))
    haveI : IsIso (X.filtration.stage (p - r + 1)).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 htop
    simpa only [FilteredObject.Hom.boundaryRepresentative,
      imageSubobject_iso_comp, FilteredObject.Hom.imageRepresentative, inf_comm]
      using hZ (Set.mem_range_self r)

private theorem cycle_isGLB_of_finite {X Y : FilteredObject C} (f : X ⟶ Y)
    (hY : Y.IsFinite) (p : ℤ) :
    IsGLB (Set.range fun r : ℕ ↦ f.cycleRepresentative r p)
      (f.kernelRepresentative p) := by
  refine ⟨?_, ?_⟩
  · show f.kernelRepresentative p ∈ lowerBounds _
    rintro _ ⟨r, rfl⟩
    apply sup_le_sup_right
    exact le_inf inf_le_right (inf_le_left.trans (kernel_le_pullback f _))
  · change ∀ Z ∈ lowerBounds _, Z ≤ f.kernelRepresentative p
    intro Z hZ
    obtain ⟨_, b, _, hb⟩ := hY
    let r : ℕ := (b - p).toNat
    have hbot : Y.filtration.stage (p + r) = ⊥ :=
      le_bot_iff.mp ((Y.filtration.antitone (by dsimp [r]; omega)).trans hb.le)
    simpa only [FilteredObject.Hom.cycleRepresentative, hbot,
      pullback_bot_eq_kernel, FilteredObject.Hom.kernelRepresentative, inf_comm]
      using hZ (Set.mem_range_self r)

/-- For an associated spectral sequence of a complex with finite term filtrations, the eventual
representatives stabilize at the intrinsic cycles and boundaries, so weak convergence holds along
any explicit eventual representatives. -/
theorem Convergence.isWeakAlong (hfinite : K.HasFiniteFiltrations)
    (hAssoc : FilteredComplex.IsAssociated K E)
    (R : FilteredComplex.Cohomology.Convergence.LimitRepresentatives K) :
    FilteredComplex.Cohomology.Convergence.IsWeakAlong K E R := by
  refine ⟨hAssoc, fun n p ↦ ⟨?_, ?_⟩⟩
  · change (R.boundary n).boundary p = Cohomology.Representative.boundary K n p
    exact ((R.boundary n).boundary_isLUB p).unique
      (boundary_isLUB_of_finite (K.d (n - 1) n) (hfinite (n - 1)) p)
  · change Cohomology.Representative.cycle K n p = (R.cycle n).cycle p
    exact (cycle_isGLB_of_finite (K.d n (n + 1)) (hfinite (n + 1)) p).unique
      ((R.cycle n).cycle_isGLB p)

/-- Finite term filtrations provide eventual representatives along which the associated spectral
sequence weakly converges. -/
theorem Convergence.isWeak (hfinite : K.HasFiniteFiltrations)
    (hAssoc : FilteredComplex.IsAssociated K E) :
    FilteredComplex.Cohomology.Convergence.IsWeak K E := by
  let L (i j : ℤ) : FilteredObject.Hom.LimitRepresentatives (K.d i j) :=
    { boundary := (K.d i j).imageRepresentative
      cycle := (K.d i j).kernelRepresentative
      boundary_isLUB := boundary_isLUB_of_finite (K.d i j) (hfinite i)
      cycle_isGLB := cycle_isGLB_of_finite (K.d i j) (hfinite j) }
  let R : FilteredComplex.Cohomology.Convergence.LimitRepresentatives K :=
    { boundary := fun n ↦ L (n - 1) n
      cycle := fun n ↦ L n (n + 1) }
  exact ⟨R, Convergence.isWeakAlong hfinite hAssoc R⟩

/-- Finite term filtrations and weak convergence assemble into convergence to cohomology.
The zeroth-page comparison needed for boundedness is already part of weak convergence through
its association component. -/
theorem Convergence.converges_of_isWeak (hfinite : K.HasFiniteFiltrations)
    (hweak : FilteredComplex.Cohomology.Convergence.IsWeak K E) :
    FilteredComplex.Cohomology.Convergence.Converges K E := by
  refine ⟨?_, ⟨hweak, Cohomology.isSeparatedExhaustive hfinite⟩,
    Cohomology.isComplete hfinite⟩
  exact (Convergence.isBounded_of_associated hfinite hweak.isAssociated).isRegular

/-- An associated spectral sequence of a termwise finitely filtered complex converges to the
cohomology of the complex. -/
@[stacks 012W, stacks 0H7W "convergence from finite term filtrations"]
theorem Convergence.converges (hfinite : K.HasFiniteFiltrations)
    (hAssoc : FilteredComplex.IsAssociated K E) :
    FilteredComplex.Cohomology.Convergence.Converges K E :=
  Convergence.converges_of_isWeak hfinite (Convergence.isWeak hfinite hAssoc)

end HasFiniteFiltrations
end FilteredComplex
end CategoryTheory
