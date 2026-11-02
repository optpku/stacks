/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.Order.Antichain
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Separation.Connected
public import ReasLib.RingTheory.Algebraic.ResidueField

/-!
# Profinite spectra along algebra maps

This module records preservation of total disconnectedness of prime spectra
under fiberwise incomparability, residue-field algebraicity, étale-related
hypotheses, and filtered colimits.
-/

@[expose] public section

open CategoryTheory Limits CommRingCat Topology

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Fibers of `Spec(S) → Spec(R)` are antichains for inclusion of primes. -/
def IsAntichainOnFibers (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  ∀ p : PrimeSpectrum R,
    IsAntichain (· ≤ ·) (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})

namespace IsAntichainOnFibers

/-- Fiberwise incomparability is equivalent to: primes over the same prime of `R`
that specialize are equal. -/
theorem iff :
    IsAntichainOnFibers R S ↔
      ∀ ⦃q q' : PrimeSpectrum S⦄,
        PrimeSpectrum.comap (algebraMap R S) q = PrimeSpectrum.comap (algebraMap R S) q' →
          q ⤳ q' → q = q' := by
  constructor
  · intro h q q' hcomap hspec
    exact (h (PrimeSpectrum.comap (algebraMap R S) q)).eq
      (show q ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹'
        ({PrimeSpectrum.comap (algebraMap R S) q} : Set (PrimeSpectrum R)) by simp)
      (show q' ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹'
        ({PrimeSpectrum.comap (algebraMap R S) q} : Set (PrimeSpectrum R)) by simp [hcomap])
      ((PrimeSpectrum.le_iff_specializes _ _).mpr hspec)
  · intro h p q hq q' hq' hne hle
    exact hne <| h ((Set.mem_singleton_iff.mp hq).trans (Set.mem_singleton_iff.mp hq').symm)
      ((PrimeSpectrum.le_iff_specializes _ _).mp hle)

/-- In an antichain fiber, specialization implies equality. -/
theorem eq_of_specializes (h : IsAntichainOnFibers R S) {q q' : PrimeSpectrum S}
    (hcomap :
      PrimeSpectrum.comap (algebraMap R S) q = PrimeSpectrum.comap (algebraMap R S) q')
    (hspec : q ⤳ q') : q = q' :=
  (iff.mp h) hcomap hspec

/-- Quasi-finite algebras have antichain fibers. -/
theorem of_quasiFinite [QuasiFinite R S] : IsAntichainOnFibers R S := by
  intro p q hq q' hq' hne hle
  exact hne <| (QuasiFinite.isDiscrete_comap_preimage_singleton p).eq_of_specializes
    ((PrimeSpectrum.le_iff_specializes _ _).mp hle) hq hq'

end IsAntichainOnFibers

end Algebra

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

private theorem isTotallyDisconnected_univ_of_specializes_imp_eq
    {A : Type*} [CommRing A]
    (h : ∀ ⦃p q : PrimeSpectrum A⦄, p ⤳ q → p = q) :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum A)) := by
  letI : T1Space (PrimeSpectrum A) := t1Space_iff_specializes_imp_eq.mpr h
  have hclosed (r : A) : IsClosed (basicOpen r : Set (PrimeSpectrum A)) := by
    rw [← localization_away_comap_range (Localization.Away r) r]
    apply isClosed_range_of_stableUnderSpecialization
    intro p q hpq hp
    simpa only [h hpq] using hp
  letI : TotallySeparatedSpace (PrimeSpectrum A) :=
    totallySeparatedSpace_iff_exists_isClopen.mpr <| by
      intro p q hpq
      obtain ⟨U, hU, hpU, hUq⟩ :=
        isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpq isClosed_singleton.isOpen_compl
      obtain ⟨r, rfl⟩ := hU
      exact ⟨_, ⟨hclosed r, (basicOpen r).isOpen⟩, hpU, fun hqU => hUq hqU rfl⟩
  exact isTotallyDisconnected_of_totallyDisconnectedSpace _

/-- If `Spec(R)` is totally disconnected and fibers of `Spec(S) → Spec(R)` are
antichains, then `Spec(S)` is totally disconnected. -/
theorem isTotallyDisconnected_univ_of_isAntichainOnFibers
    [TotallyDisconnectedSpace (PrimeSpectrum R)]
    (h : Algebra.IsAntichainOnFibers R S) :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) := by
  apply isTotallyDisconnected_univ_of_specializes_imp_eq
  intro q q' hspec
  exact h.eq_of_specializes
    (hspec.map (PrimeSpectrum.continuous_comap (algebraMap R S))).eq hspec

/-- If `Spec(R)` is totally disconnected and residue-field extensions are algebraic,
then `Spec(S)` is totally disconnected. -/
theorem isTotallyDisconnected_univ_of_isAlgebraicOnResidueFields
    [TotallyDisconnectedSpace (PrimeSpectrum R)]
    (h : Algebra.IsAlgebraicOnResidueFields R S) :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) := by
  apply isTotallyDisconnected_univ_of_specializes_imp_eq
  intro q q' hspec
  let p := PrimeSpectrum.comap (algebraMap R S) q
  letI : p.asIdeal.IsMaximal :=
    (isClosed_singleton_iff_isMaximal p).mp isClosed_singleton
  letI : Field (R ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  let f := Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S) rfl
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := f.toAlgebra
  letI : Algebra (R ⧸ p.asIdeal) q.asIdeal.ResidueField :=
    (f.comp (algebraMap (R ⧸ p.asIdeal) p.asIdeal.ResidueField)).toAlgebra
  letI : Algebra.IsAlgebraic p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    ⟨fun x => h q x⟩
  letI : Algebra.IsAlgebraic (R ⧸ p.asIdeal) q.asIdeal.ResidueField :=
    Algebra.IsAlgebraic.of_ringHom_of_comp_eq
      (algebraMap (R ⧸ p.asIdeal) p.asIdeal.ResidueField)
      (RingHom.id q.asIdeal.ResidueField)
      p.asIdeal.bijective_algebraMap_quotient_residueField.surjective Function.injective_id rfl
  letI : IsScalarTower (R ⧸ p.asIdeal) (S ⧸ q.asIdeal) q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext x
      change f (algebraMap R p.asIdeal.ResidueField x) =
        algebraMap (S ⧸ q.asIdeal) q.asIdeal.ResidueField
          (Ideal.Quotient.mk q.asIdeal (algebraMap R S x))
      rw [Ideal.algebraMap_quotient_residueField_mk]
      exact Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal (algebraMap R S) rfl x
  letI : Algebra.IsAlgebraic (R ⧸ p.asIdeal) (S ⧸ q.asIdeal) :=
    Algebra.IsAlgebraic.of_injective
      (IsScalarTower.toAlgHom (R ⧸ p.asIdeal) (S ⧸ q.asIdeal) q.asIdeal.ResidueField)
      q.asIdeal.injective_algebraMap_quotient_residueField
  have hmax : q.asIdeal.IsMaximal := Ideal.Quotient.maximal_of_isField _
    (isField_of_isIntegral_of_isField' (Field.toIsField (R ⧸ p.asIdeal)))
  exact PrimeSpectrum.ext (hmax.eq_of_le q'.2.ne_top
    ((PrimeSpectrum.le_iff_specializes _ _).mpr hspec))

/-- A local isomorphism preserves total disconnectedness of prime spectra. -/
theorem isTotallyDisconnected_univ_of_isLocalIso
    [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.IsLocalIso R S] :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) := by
  apply isTotallyDisconnected_univ_of_specializes_imp_eq
  intro q q' hspec
  obtain ⟨g, hg, hstd⟩ :=
    Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := R) q'.asIdeal
  letI := hstd
  obtain ⟨r, hr⟩ := Algebra.IsStandardOpenImmersion.exists_away R (Localization.Away g)
  letI := hr
  letI : Algebra.QuasiFinite R (Localization.Away g) :=
    Algebra.QuasiFinite.of_isLocalization (R := R) (S := R) (Submonoid.powers r)
  letI : TotallyDisconnectedSpace (PrimeSpectrum (Localization.Away g)) :=
    ⟨isTotallyDisconnected_univ_of_isAntichainOnFibers
      (Algebra.IsAntichainOnFibers.of_quasiFinite (R := R))⟩
  have hgq : g ∉ q.asIdeal := fun h => hg ((le_iff_specializes _ _).mpr hspec h)
  obtain ⟨a, ha⟩ := (localization_away_comap_range (Localization.Away g) g).ge hgq
  obtain ⟨b, hb⟩ := (localization_away_comap_range (Localization.Away g) g).ge hg
  have hab : a ⤳ b :=
    (localization_comap_isEmbedding (Localization.Away g) (Submonoid.powers g)).isInducing.specializes_iff.mp
      (by simpa only [ha, hb] using hspec)
  exact ha.symm.trans ((congrArg (comap (algebraMap S (Localization.Away g))) hab.eq).trans hb)

/-- A weakly étale algebra over a ring with totally disconnected spectrum again
has totally disconnected spectrum. -/
theorem isTotallyDisconnected_univ_of_weaklyEtale
    [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.WeaklyEtale R S] :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) := sorry

/-- A finite-type quasi-finite algebra over a ring with totally disconnected
spectrum again has totally disconnected spectrum. -/
theorem isTotallyDisconnected_univ_of_quasiFinite
    [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.FiniteType R S]
    [Algebra.QuasiFinite R S] :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) :=
  isTotallyDisconnected_univ_of_isAntichainOnFibers
    (Algebra.IsAntichainOnFibers.of_quasiFinite (R := R) (S := S))

/-- An unramified algebra over a ring with totally disconnected spectrum again
has totally disconnected spectrum. -/
theorem isTotallyDisconnected_univ_of_unramified
    [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.Unramified R S] :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) :=
  isTotallyDisconnected_univ_of_quasiFinite (R := R) (S := S)

/-- An étale algebra over a ring with totally disconnected spectrum again has
totally disconnected spectrum. -/
theorem isTotallyDisconnected_univ_of_etale
    [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.Etale R S] :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) :=
  isTotallyDisconnected_univ_of_quasiFinite (R := R) (S := S)

end PrimeSpectrum

namespace PrimeSpectrum

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Identifying local rings preserves total disconnectedness of prime spectra. -/
theorem isTotallyDisconnected_univ_of_isIsoOnLocalRings
    [TotallyDisconnectedSpace (PrimeSpectrum R)]
    (h : (algebraMap R S).IsIsoOnLocalRings) :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) := by
  apply isTotallyDisconnected_univ_of_isAlgebraicOnResidueFields (R := R) (S := S)
  intro q x
  have hsurj : Function.Surjective
      (Ideal.ResidueField.map (comap (algebraMap R S) q).asIdeal q.asIdeal
        (algebraMap R S) rfl) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _
      (Ideal.Quotient.mk_surjective.comp (h q).surjective)
  obtain ⟨y, rfl⟩ := hsurj x
  refine ⟨Polynomial.X - Polynomial.C y, Polynomial.X_sub_C_ne_zero y, ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_self]

end PrimeSpectrum

namespace PrimeSpectrum

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {J : Type v} [Category.{v} J] [IsFiltered J]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_stage_of_isColimit
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c) (x : c.pt) :
    ∃ (j : J) (y : F.obj j), (c.ι.app j).hom y = x := by
  letI : Nonempty J := IsFiltered.nonempty
  let f (j : J) : F.obj j →+* c.pt := (c.ι.app j).hom
  let B : Subring c.pt := ⨆ j, (f j).range
  have hle {i j : J} (g : i ⟶ j) : (f i).range ≤ (f j).range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(F.map g).hom y, ConcreteCategory.congr_hom (c.w g) y⟩
  have hdir : Directed (· ≤ ·) (fun j => (f j).range) := by
    intro i j
    exact ⟨IsFiltered.max i j, hle (IsFiltered.leftToMax i j), hle (IsFiltered.rightToMax i j)⟩
  let d : Cocone F :=
    { pt := CommRingCat.of B
      ι :=
        { app := fun j => CommRingCat.ofHom ((f j).codRestrict B
            (fun y => le_iSup (fun k => (f k).range) j ⟨y, rfl⟩))
          naturality := by
            intro i j g
            ext y
            apply Subtype.ext
            exact ConcreteCategory.congr_hom (c.w g) y } }
  let incl : d.pt ⟶ c.pt := CommRingCat.ofHom B.subtype
  have hi (j : J) : d.ι.app j ≫ incl = c.ι.app j := rfl
  have hid : hc.desc d ≫ incl = 𝟙 c.pt := by
    apply hc.hom_ext
    intro j
    rw [← Category.assoc, hc.fac d j, hi, Category.comp_id]
  have hx : x ∈ B := by
    have hmem := ((hc.desc d).hom x).property
    have heq : B.subtype ((hc.desc d).hom x) = x := ConcreteCategory.congr_hom hid x
    exact heq ▸ hmem
  obtain ⟨j, hj⟩ := (Subring.mem_iSup_of_directed hdir).mp hx
  obtain ⟨y, hy⟩ := hj
  exact ⟨j, y, hy⟩

set_option backward.isDefEq.respectTransparency false in
/-- A filtered colimit of algebras with totally disconnected spectra again has
totally disconnected spectrum. -/
theorem isTotallyDisconnected_univ_of_isColimit
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    (e : c.pt ≅ Under.mk (CommRingCat.ofHom (algebraMap R A)))
    (hF : ∀ j, IsTotallyDisconnected
      (Set.univ : Set (PrimeSpectrum (F.obj j).right))) :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum A)) := by
  letI : IsConnected J := IsFiltered.isConnected J
  apply isTotallyDisconnected_univ_of_specializes_imp_eq
  intro p q hpq
  have hstage (j : J) :
      comap ((c.ι.app j).right ≫ e.hom.right).hom p =
        comap ((c.ι.app j).right ≫ e.hom.right).hom q := by
    letI : TotallyDisconnectedSpace (PrimeSpectrum (F.obj j).right) := ⟨hF j⟩
    exact (hpq.map (continuous_comap _)).eq
  apply PrimeSpectrum.ext
  ext x
  obtain ⟨j, y, hy⟩ := exists_stage_of_isColimit
    (F ⋙ Under.forget (CommRingCat.of R)) ((Under.forget (CommRingCat.of R)).mapCocone c)
    (isColimitOfPreserves (Under.forget (CommRingCat.of R)) hc) (e.inv.right.hom x)
  change (c.ι.app j).right.hom y = e.inv.right.hom x at hy
  have hx : ((c.ι.app j).right ≫ e.hom.right).hom y = x := by
    change e.hom.right.hom ((c.ι.app j).right.hom y) = x
    rw [hy]
    exact ConcreteCategory.congr_hom (congrArg (fun f => f.right) e.inv_hom_id) x
  have hmem : ((c.ι.app j).right ≫ e.hom.right).hom y ∈ p.asIdeal ↔
      ((c.ι.app j).right ≫ e.hom.right).hom y ∈ q.asIdeal := by
    change y ∈ (comap _ p).asIdeal ↔ y ∈ (comap _ q).asIdeal
    rw [hstage j]
  simpa only [hx] using hmem

end PrimeSpectrum
