/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Map
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Principal Opens and Localization Comparison Maps

This module packages the ring- and module-theoretic consequences of an
inclusion of principal opens of `PrimeSpectrum R`.  The topology remains in
the canonical `PrimeSpectrum` namespace, while the comparison maps expose the
ordinary localization data used by affine and sheaf-theoretic applications.
-/

noncomputable section

universe u v

namespace PrimeSpectrum

section

variable {R : Type u} [CommSemiring R]
variable (f g : R)

/-- An inclusion `D(g) ≤ D(f)` makes the image of `f` invertible in `R_g`. -/
@[stacks 01HS]
theorem algebraMap_isUnit_of_basicOpen_le
    (h : basicOpen g ≤ basicOpen f) :
    IsUnit (algebraMap R (Localization.Away g) f) := by
  exact basicOpen_le_basicOpen_iff_algebraMap_isUnit.mp h

/-- An inclusion `D(g) ≤ D(f)` implies that a positive power of `g` is a
multiple of `f`. -/
@[stacks 01HS]
theorem exists_pow_eq_mul_of_basicOpen_le
    (h : basicOpen g ≤ basicOpen f) :
    ∃ e : ℕ, 0 < e ∧ ∃ a : R, g ^ e = a * f := by
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ((basicOpen_le_basicOpen_iff g f).mp h)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hn
  refine ⟨n + 1, Nat.succ_pos n, g * a, ?_⟩
  calc
    g ^ (n + 1) = g * g ^ n := pow_succ' g n
    _ = g * (a * f) := congrArg (g * ·) ha.symm
    _ = (g * a) * f := (mul_assoc g a f).symm

/-- Inclusion of principal opens is equivalent to a positive power of the
smaller-open generator being a multiple of the larger-open generator. -/
@[stacks 01HS "principal-open inclusion criterion"]
theorem basicOpen_le_basicOpen_iff_exists_pow_eq_mul :
    basicOpen g ≤ basicOpen f ↔ ∃ e : ℕ, 0 < e ∧ ∃ a : R, g ^ e = a * f := by
  constructor
  · exact exists_pow_eq_mul_of_basicOpen_le f g
  · rintro ⟨e, _, a, ha⟩
    apply (basicOpen_le_basicOpen_iff g f).mpr
    exact Ideal.mem_radical_iff.mpr ⟨e, Ideal.mem_span_singleton'.mpr ⟨a, ha.symm⟩⟩

/-- The localization comparison as an `R`-algebra homomorphism, attached to an
inclusion `D(g) ≤ D(f)`. -/
@[stacks 01HS "principal-open localization algebra map"]
noncomputable def awayToAwayAlgHom
    (h : basicOpen g ≤ basicOpen f) :
    Localization.Away f →ₐ[R] Localization.Away g :=
  IsLocalization.Away.liftAlgHom
    (S := Localization.Away f) (P := Localization.Away g) (A := R)
    (f := Algebra.ofId R (Localization.Away g)) f
    (basicOpen_le_basicOpen_iff_algebraMap_isUnit.mp h)

/-- The restriction algebra map commutes with the maps from the original semiring. -/
@[simp, stacks 01HS "principal-open localization algebra map law"]
theorem awayToAwayAlgHom_algebraMap
    (h : basicOpen g ≤ basicOpen f) (r : R) :
    awayToAwayAlgHom f g h (algebraMap R (Localization.Away f) r) =
      algebraMap R (Localization.Away g) r := by
  exact (awayToAwayAlgHom f g h).commutes r

/-- Restriction from a principal open to itself is the identity algebra map. -/
@[simp, stacks 01HS "principal-open localization algebra identity"]
theorem awayToAwayAlgHom_self :
    awayToAwayAlgHom f f le_rfl = AlgHom.id R (Localization.Away f) := by
  letI : Subsingleton (Localization.Away f →ₐ[R] Localization.Away f) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers f)
  exact Subsingleton.elim _ _

/-- Comparison algebra homomorphisms compose along nested principal-open
inclusions. -/
@[stacks 01HS "principal-open localization algebra composition"]
theorem awayToAwayAlgHom_comp
    {q : R} (hfg : basicOpen g ≤ basicOpen f) (hgq : basicOpen q ≤ basicOpen g) :
    (awayToAwayAlgHom g q hgq).comp (awayToAwayAlgHom f g hfg) =
      awayToAwayAlgHom f q (hgq.trans hfg) := by
  letI : Subsingleton (Localization.Away f →ₐ[R] Localization.Away q) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers f)
  exact Subsingleton.elim _ _

/-- The localization comparison algebra map is determined by its values on the original
semiring. -/
@[stacks 01HS "principal-open localization algebra uniqueness"]
theorem awayToAwayAlgHom_unique
    (h : basicOpen g ≤ basicOpen f)
    (phi : Localization.Away f →ₐ[R] Localization.Away g)
    (hphi : ∀ r : R,
      phi (algebraMap R (Localization.Away f) r) =
        algebraMap R (Localization.Away g) r) :
    phi = awayToAwayAlgHom f g h := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  simpa using hphi r

/-- The localization comparison ring homomorphism `R_f → R_g` attached to
`D(g) ≤ D(f)`. -/
@[stacks 01HS]
noncomputable abbrev awayToAwayRingHom
    (h : basicOpen g ≤ basicOpen f) :
    Localization.Away f →+* Localization.Away g :=
  (awayToAwayAlgHom f g h).toRingHom

/-- The ring-hom view is definitionally the underlying hom of the restriction algebra map. -/
@[simp, stacks 01HS "principal-open localization ring bridge"]
theorem awayToAwayAlgHom_toRingHom
    (h : basicOpen g ≤ basicOpen f) :
    (awayToAwayAlgHom f g h).toRingHom = awayToAwayRingHom f g h := by
  rfl

/-- The localization comparison `R_f → R_g` commutes with the maps from
`R`. -/
@[simp, stacks 01HS "principal-open localization ring map law"]
theorem awayToAwayRingHom_algebraMap
    (h : basicOpen g ≤ basicOpen f) (r : R) :
    awayToAwayRingHom f g h (algebraMap R (Localization.Away f) r) =
      algebraMap R (Localization.Away g) r := by
  exact awayToAwayAlgHom_algebraMap f g h r

/-- Restriction from a principal open to itself is the identity ring homomorphism. -/
@[simp, stacks 01HS "principal-open localization ring identity"]
theorem awayToAwayRingHom_self :
    awayToAwayRingHom f f le_rfl = RingHom.id (Localization.Away f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  simp

/-- Comparison ring homomorphisms compose along nested principal-open
inclusions. -/
@[stacks 01HS "principal-open localization ring composition"]
theorem awayToAwayRingHom_comp
    {q : R} (hfg : basicOpen g ≤ basicOpen f) (hgq : basicOpen q ≤ basicOpen g) :
    (awayToAwayRingHom g q hgq).comp (awayToAwayRingHom f g hfg) =
      awayToAwayRingHom f q (hgq.trans hfg) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  simp

/-- The localization comparison ring homomorphism is determined by its values on the original
semiring. -/
@[stacks 01HS "principal-open localization ring uniqueness"]
theorem awayToAwayRingHom_unique
    (h : basicOpen g ≤ basicOpen f)
    (phi : Localization.Away f →+* Localization.Away g)
    (hphi : ∀ r : R,
      phi (algebraMap R (Localization.Away f) r) =
        algebraMap R (Localization.Away g) r) :
    phi = awayToAwayRingHom f g h := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  simpa using hphi r

section ModuleMap

/-- The underlying `R`-linear map used to construct restriction of a localized module from
`D(f)` to `D(g)`. -/
@[stacks 01HS "principal-open localized module linear map"]
noncomputable abbrev awayToAwayModuleLinearMap
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f) :
    LocalizedModule.Away f M →ₗ[R] LocalizedModule.Away g M :=
  LocalizedModule.Away.mapOfIsUnit f g
    (basicOpen_le_basicOpen_iff_algebraMap_isUnit.mp h)

private theorem awayModuleLinearMap_mk
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f) (m : M) :
    awayToAwayModuleLinearMap M f g h
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers g) M m := by
  simp [awayToAwayModuleLinearMap, LocalizedModule.Away.mapOfIsUnit,
    LocalizedModule.mkLinearMap_apply, Localization.mk_one_eq_algebraMap]

private theorem awayModuleLinearMap_ext
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f)
    {phi psi : LocalizedModule.Away f M →ₗ[R] LocalizedModule.Away g M}
    (hphi : ∀ m : M,
      phi (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
        psi (LocalizedModule.mkLinearMap (Submonoid.powers f) M m)) : phi = psi := by
  apply IsLocalizedModule.ext (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
  · rintro ⟨_, ⟨n, rfl⟩⟩
    rw [← (Algebra.lsmul R (A := Localization.Away g) R
      (LocalizedModule.Away g M)).commutes]
    simpa only [map_pow] using
      ((algebraMap_isUnit_of_basicOpen_le f g h).pow n).map
        (Algebra.lsmul R (A := Localization.Away g) R (LocalizedModule.Away g M))
  · ext m
    exact hphi m

/-- Restriction of a localized module to the same principal open is the identity on the
underlying `R`-module. -/
@[simp, stacks 01HS "principal-open localized module linear identity"]
theorem awayToAwayModuleLinearMap_self
    (M : Type v) [AddCommMonoid M] [Module R M] (f : R) :
    awayToAwayModuleLinearMap M f f le_rfl = LinearMap.id := by
  apply awayModuleLinearMap_ext M f f le_rfl
  intro m
  simp only [awayModuleLinearMap_mk, LinearMap.id_apply]

/-- Underlying `R`-linear restriction maps compose along inclusions of principal opens. -/
@[stacks 01HS "principal-open localized module linear composition"]
theorem awayToAwayModuleLinearMap_comp
    (M : Type v) [AddCommMonoid M] [Module R M] (f g q : R)
    (hfg : basicOpen g ≤ basicOpen f) (hgq : basicOpen q ≤ basicOpen g) :
    (awayToAwayModuleLinearMap M g q hgq).comp
        (awayToAwayModuleLinearMap M f g hfg) =
      awayToAwayModuleLinearMap M f q (hgq.trans hfg) := by
  apply awayModuleLinearMap_ext M f q (hgq.trans hfg)
  intro m
  simp only [LinearMap.comp_apply, awayModuleLinearMap_mk]

/-- The underlying localized-module comparison is determined by its values on elements coming
from the original module. -/
@[stacks 01HS "principal-open localized module linear uniqueness"]
theorem awayToAwayModuleLinearMap_unique
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f)
    (phi : LocalizedModule.Away f M →ₗ[R] LocalizedModule.Away g M)
    (hphi : ∀ m : M,
      phi (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
        LocalizedModule.mkLinearMap (Submonoid.powers g) M m) :
    phi = awayToAwayModuleLinearMap M f g h := by
  apply awayModuleLinearMap_ext M f g h
  intro m
  rw [hphi, awayModuleLinearMap_mk]

/-- The underlying restriction map is semilinear over the canonical map between the localized
semirings. -/
@[stacks 01HS "principal-open localized module semilinearity"]
theorem awayToAwayModuleLinearMap_smul
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f) (r : Localization.Away f)
    (x : LocalizedModule.Away f M) :
    awayToAwayModuleLinearMap M f g h (r • x) =
      awayToAwayRingHom f g h r • awayToAwayModuleLinearMap M f g h x := by
  let F := awayToAwayAlgHom f g h
  let T := TensorProduct.map F.toLinearMap (LinearMap.id : M →ₗ[R] M)
  have hT (z : TensorProduct R (Localization.Away f) M) : T (r • z) = F r • T z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp [T, TensorProduct.smul_tmul', smul_eq_mul]
    | add a b ha hb => simp [smul_add, ha, hb]
  change (LocalizedModule.equivTensorProduct (Submonoid.powers g) M).symm
      (T (LocalizedModule.equivTensorProduct (Submonoid.powers f) M (r • x))) =
    F r • (LocalizedModule.equivTensorProduct (Submonoid.powers g) M).symm
      (T (LocalizedModule.equivTensorProduct (Submonoid.powers f) M x))
  rw [map_smul, hT, map_smul]

/-- Restriction `M_f ⟶ M_g` is semilinear over the canonical localization
homomorphism `R_f ⟶ R_g`. -/
@[stacks 01HS]
noncomputable def awayToAwayModuleMap
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f) :
    LocalizedModule.Away f M →ₛₗ[awayToAwayRingHom f g h]
      LocalizedModule.Away g M :=
  { toFun := awayToAwayModuleLinearMap M f g h
    map_add' := (awayToAwayModuleLinearMap M f g h).map_add
    map_smul' := awayToAwayModuleLinearMap_smul M f g h }

/-- The semilinear restriction map has the underlying function of the canonical `R`-linear
restriction map. -/
@[simp, stacks 01HS "principal-open localized module map evaluation"]
theorem awayToAwayModuleMap_apply
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f) (x : LocalizedModule.Away f M) :
    awayToAwayModuleMap M f g h x = awayToAwayModuleLinearMap M f g h x := by
  rfl

/-- Restriction of a localized module to the same principal open is the identity. -/
@[simp, stacks 01HS "principal-open localized module identity"]
theorem awayToAwayModuleMap_self_apply
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f : R) (x : LocalizedModule.Away f M) :
    awayToAwayModuleMap M f f le_rfl x = x := by
  change awayToAwayModuleLinearMap M f f le_rfl x = x
  rw [awayToAwayModuleLinearMap_self]
  rfl

/-- Semilinear restriction maps compose pointwise along inclusions of principal opens. -/
@[simp, stacks 01HS "principal-open localized module composition"]
theorem awayToAwayModuleMap_comp_apply
    (M : Type v) [AddCommMonoid M] [Module R M] (f g q : R)
    (hfg : basicOpen g ≤ basicOpen f) (hgq : basicOpen q ≤ basicOpen g)
    (x : LocalizedModule.Away f M) :
    awayToAwayModuleMap M g q hgq (awayToAwayModuleMap M f g hfg x) =
      awayToAwayModuleMap M f q (hgq.trans hfg) x := by
  exact LinearMap.congr_fun (awayToAwayModuleLinearMap_comp M f g q hfg hgq) x

/-- The semilinear localization comparison commutes with the canonical maps from the original
module. -/
@[simp, stacks 01HS "principal-open localized module map law"]
theorem awayToAwayModuleMap_mkLinearMap
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f) (m : M) :
    awayToAwayModuleMap M f g h
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers g) M m := by
  exact awayModuleLinearMap_mk M f g h m

/-- The semilinear localization comparison is determined by its values on elements coming from
the original module. -/
@[stacks 01HS "principal-open localized module map uniqueness"]
theorem awayToAwayModuleMap_unique
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f g : R) (h : basicOpen g ≤ basicOpen f)
    (phi : LocalizedModule.Away f M →ₛₗ[awayToAwayRingHom f g h]
      LocalizedModule.Away g M)
    (hphi : ∀ m : M,
      phi (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
        LocalizedModule.mkLinearMap (Submonoid.powers g) M m) :
    phi = awayToAwayModuleMap M f g h := by
  let phiR : LocalizedModule.Away f M →ₗ[R] LocalizedModule.Away g M :=
    { toFun := phi
      map_add' := phi.map_add
      map_smul' := fun r x ↦ by
        rw [← IsScalarTower.algebraMap_smul (Localization.Away f) r x,
          phi.map_smulₛₗ, awayToAwayRingHom_algebraMap,
          IsScalarTower.algebraMap_smul]
        rfl }
  have hR : phiR = awayToAwayModuleLinearMap M f g h :=
    awayToAwayModuleLinearMap_unique M f g h phiR hphi
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun hR x

end ModuleMap

/-- Every open cover of `D(f)` has a finite refinement indexed by a `Finset` of principal-open
generators, each contained in a member of the original cover. -/
@[stacks 01HS]
theorem basicOpen_has_finset_refinement_of_open_cover
    {ι : Type v} (U : ι → TopologicalSpace.Opens (PrimeSpectrum R))
    (hcover : basicOpen f ≤ ⨆ i, U i) :
    ∃ s : Finset R,
      basicOpen f = ⨆ g ∈ s, basicOpen g ∧
        ∀ g ∈ s, ∃ i, basicOpen g ≤ U i := by
  classical
  let G := {g : R // basicOpen g ≤ basicOpen f ∧ ∃ i, basicOpen g ≤ U i}
  have hG : basicOpen f ≤ ⨆ g : G, basicOpen g.1 := by
    intro p hp
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover hp)
    obtain ⟨_, ⟨g, rfl⟩, hpg, hg⟩ :=
      isTopologicalBasis_basic_opens.isOpen_iff.mp (U i ⊓ basicOpen f).isOpen p ⟨hi, hp⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨g, (fun _ hx ↦ (hg hx).2), i, (fun _ hx ↦ (hg hx).1)⟩, hpg⟩
  obtain ⟨t, ht⟩ := (isCompact_basicOpen f).elim_finite_subcover
    (fun g : G ↦ (basicOpen g.1 : Set (PrimeSpectrum R)))
    (fun g ↦ (basicOpen g.1).isOpen) (by
      simpa only [TopologicalSpace.Opens.coe_iSup] using
        (SetLike.coe_subset_coe.mpr hG))
  refine ⟨t.image Subtype.val, le_antisymm ?_ ?_, ?_⟩
  · intro p hp
    obtain ⟨g, hgt, hpg⟩ := Set.mem_iUnion₂.mp (ht hp)
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨g.1, TopologicalSpace.Opens.mem_iSup.mpr ⟨Finset.mem_image_of_mem _ hgt, hpg⟩⟩
  · refine iSup_le fun g ↦ iSup_le fun hg ↦ ?_
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hg
    exact k.2.1
  · intro g hg
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hg
    exact k.2.2

/-- Every open cover of `D(f)` has a refinement by a finite indexed family of
principal opens. -/
@[stacks 01HS]
theorem basicOpen_has_finite_refinement_of_open_cover
    {ι : Type v} (U : ι → TopologicalSpace.Opens (PrimeSpectrum R))
    (hcover : basicOpen f ≤ ⨆ i, U i) :
    ∃ (sigma : Type v) (_ : Finite sigma) (g' : sigma → R),
      basicOpen f = ⨆ i, basicOpen (g' i) ∧
        ∀ i, ∃ j, basicOpen (g' i) ≤ U j := by
  classical
  obtain ⟨s, hs, href⟩ := basicOpen_has_finset_refinement_of_open_cover f U hcover
  refine ⟨ULift.{v} (Fin s.card), inferInstance,
    (fun i ↦ (s.equivFin.symm i.down).1), ?_, ?_⟩
  · rw [hs]
    apply le_antisymm
    · refine iSup_le fun g ↦ iSup_le fun hg ↦ ?_
      exact le_iSup_of_le ⟨s.equivFin ⟨g, hg⟩⟩ (by simp)
    · refine iSup_le fun i ↦ ?_
      exact le_iSup_of_le (s.equivFin.symm i.down).1
        (le_iSup_of_le (s.equivFin.symm i.down).2 le_rfl)
  · intro i
    exact href _ (s.equivFin.symm i.down).2

/-- A family of principal opens covers `D(f)` exactly when its generators span
the unit ideal after localizing away from `f`. -/
@[stacks 01HS]
theorem basicOpen_le_iSup_basicOpen_iff_span_eq_top
    {ι : Type v} (g' : ι → R) :
    basicOpen f ≤ ⨆ i, basicOpen (g' i) ↔
      Ideal.span (Set.range fun i : ι ↦ algebraMap R (Localization.Away f) (g' i)) = ⊤ := by
  rw [← iSup_basicOpen_eq_top_iff]
  constructor
  · intro h
    apply top_unique
    intro p _
    have hp : comap (algebraMap R (Localization.Away f)) p ∈ basicOpen f :=
      (localization_away_comap_range (Localization.Away f) f).le (Set.mem_range_self p)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (h hp)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro h p hp
    have hp' : p ∈ Set.range (comap (algebraMap R (Localization.Away f))) :=
      (localization_away_comap_range (Localization.Away f) f).ge hp
    obtain ⟨q, rfl⟩ := hp'
    have hq : q ∈ ⨆ i, basicOpen (algebraMap R (Localization.Away f) (g' i)) := by
      rw [h]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hq
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

end

end PrimeSpectrum
