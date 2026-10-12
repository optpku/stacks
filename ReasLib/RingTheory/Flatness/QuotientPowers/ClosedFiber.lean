/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Quotient
public import ReasLib.LinearAlgebra.QuotientByIdeal.Mapped
public import ReasLib.RingTheory.Flat.Localization.AtPrime
public import ReasLib.RingTheory.Ideal.Quotient.Prime
public import ReasLib.RingTheory.Localization.AtPrime.Relative
public import ReasLib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Closed fibers of localized quotient modules

This leaf transports flatness of `M / ISM` over `R / I` to the corresponding
quotient of `M_q`.  It keeps the quotient-prime localization and the relative
prime-localization scalar actions local to the proof.

@stack 0523
-/

@[expose] public section

universe u v w

open scoped Pointwise

namespace Module.Flat

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

omit [Module R M] [IsScalarTower R S M] in
private lemma localizedMappedIdeal_smulTop_eq
    (I : Ideal R) (q : PrimeSpectrum S) :
    let Sq := Localization.AtPrime q.asIdeal
    let Mq := LocalizedModule.AtPrime q.asIdeal M
    let IS := Ideal.map (algebraMap R S) I
    let K := Ideal.map (algebraMap S Sq) IS
    (IS • (⊤ : Submodule S M)).localized q.asIdeal.primeCompl =
      K • (⊤ : Submodule Sq Mq) := by
  intro Sq Mq IS K
  rw [Submodule.localized, Submodule.localized'_smul, Ideal.localized'_eq_map,
    Submodule.localized'_top]

private noncomputable def localizedMappedIdealQuotientEquiv
    (I : Ideal R) (q : PrimeSpectrum S) :
    let Sq := Localization.AtPrime q.asIdeal
    let Mq := LocalizedModule.AtPrime q.asIdeal M
    let IS := Ideal.map (algebraMap R S) I
    let K := Ideal.map (algebraMap S Sq) IS
    LocalizedModule.AtPrime q.asIdeal
        (M ⧸ (IS • (⊤ : Submodule S M))) ≃ₗ[Sq]
      Mq ⧸ (K • (⊤ : Submodule Sq Mq)) :=
  let IS := Ideal.map (algebraMap R S) I
  (localizedQuotientEquiv q.asIdeal.primeCompl
      (IS • (⊤ : Submodule S M))).symm.trans
    (Submodule.quotEquivOfEq _ _
      (localizedMappedIdeal_smulTop_eq (R := R) (S := S) (M := M) I q))

private noncomputable def closedFiberMap
    (I : Ideal R) (q : PrimeSpectrum S) :
    let Sq := Localization.AtPrime q.asIdeal
    let Mq := LocalizedModule.AtPrime q.asIdeal M
    let IS := Ideal.map (algebraMap R S) I
    let Bbar := S ⧸ IS
    let Qbar := M ⧸ (IS • (⊤ : Submodule S M))
    let K := Ideal.map (algebraMap S Sq) IS
    let Tgt := Mq ⧸ (K • (⊤ : Submodule Sq Mq))
    Qbar →ₗ[Bbar] Tgt := by
  intro Sq Mq IS Bbar Qbar K Tgt
  let e : LocalizedModule.AtPrime q.asIdeal Qbar ≃ₗ[Sq] Tgt :=
    localizedMappedIdealQuotientEquiv (R := R) (S := S) (M := M) I q
  let f : Qbar →ₗ[S] Tgt :=
    (e.restrictScalars S).toLinearMap.comp
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl Qbar)
  exact LinearMap.extendScalarsOfSurjective
    (R := S) (S := Bbar) Ideal.Quotient.mk_surjective f

omit [Module R M] [IsScalarTower R S M] in
private lemma closedFiberMap_isLocalizedModule
    (I : Ideal R) (q : PrimeSpectrum S)
    (hq : Ideal.map (algebraMap R S) I ≤ q.asIdeal) :
    let IS := Ideal.map (algebraMap R S) I
    let qbar := PrimeSpectrum.quotientOfLE IS q hq
    IsLocalizedModule qbar.asIdeal.primeCompl
      (closedFiberMap (R := R) (S := S) (M := M) I q) := by
  intro IS qbar
  let Bbar := S ⧸ IS
  let Sq := Localization.AtPrime q.asIdeal
  let Mq := LocalizedModule.AtPrime q.asIdeal M
  let Qbar := M ⧸ (IS • (⊤ : Submodule S M))
  let K := Ideal.map (algebraMap S Sq) IS
  let Tgt := Mq ⧸ (K • (⊤ : Submodule Sq Mq))
  let e : LocalizedModule.AtPrime q.asIdeal Qbar ≃ₗ[Sq] Tgt :=
    localizedMappedIdealQuotientEquiv (R := R) (S := S) (M := M) I q
  let f : Qbar →ₗ[S] Tgt :=
    (e.restrictScalars S).toLinearMap.comp
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl Qbar)
  have hf : IsLocalizedModule q.asIdeal.primeCompl f :=
    IsLocalizedModule.of_linearEquiv q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl Qbar) (e.restrictScalars S)
  let fbar : Qbar →ₗ[Bbar] Tgt :=
    LinearMap.extendScalarsOfSurjective
      (R := S) (S := Bbar) Ideal.Quotient.mk_surjective f
  have hrestrict : IsLocalizedModule q.asIdeal.primeCompl (fbar.restrictScalars S) := by
    change IsLocalizedModule q.asIdeal.primeCompl f
    exact hf
  letI : IsLocalizedModule q.asIdeal.primeCompl (fbar.restrictScalars S) := hrestrict
  have hbar :
      IsLocalizedModule (Algebra.algebraMapSubmonoid Bbar q.asIdeal.primeCompl) fbar :=
    IsLocalizedModule.of_restrictScalars q.asIdeal.primeCompl fbar
  have hprimeCompl :
      Algebra.algebraMapSubmonoid Bbar q.asIdeal.primeCompl = qbar.asIdeal.primeCompl := by
    simpa [Bbar, qbar] using PrimeSpectrum.quotientOfLE_primeCompl IS q hq
  simpa [closedFiberMap, Sq, Mq, IS, Bbar, Qbar, K, Tgt, e, f, fbar,
    hprimeCompl] using hbar

private noncomputable def closedFiberEquiv
    (I : Ideal R) (q : PrimeSpectrum S)
    (hq : Ideal.map (algebraMap R S) I ≤ q.asIdeal) :
    let Sq := Localization.AtPrime q.asIdeal
    let Mq := LocalizedModule.AtPrime q.asIdeal M
    let IS := Ideal.map (algebraMap R S) I
    let Bbar := S ⧸ IS
    let Qbar := M ⧸ (IS • (⊤ : Submodule S M))
    let K := Ideal.map (algebraMap S Sq) IS
    let Tgt := Mq ⧸ (K • (⊤ : Submodule Sq Mq))
    let qbar := PrimeSpectrum.quotientOfLE IS q hq
    LocalizedModule.AtPrime qbar.asIdeal Qbar ≃ₗ[Bbar] Tgt := by
  intro Sq Mq IS Bbar Qbar K Tgt qbar
  letI : IsLocalizedModule qbar.asIdeal.primeCompl
      (closedFiberMap (R := R) (S := S) (M := M) I q) :=
    closedFiberMap_isLocalizedModule (R := R) (S := S) (M := M) I q hq
  exact IsLocalizedModule.iso qbar.asIdeal.primeCompl
    (closedFiberMap (R := R) (S := S) (M := M) I q)

omit [Module R M] [IsScalarTower R S M] in
/-- Flatness of the mapped-ideal quotient survives localization at a target prime containing
the mapped ideal.  The conclusion retains the canonical quotient by the localized target ideal. -/
@[stacks 0523 "localized closed-fiber quotient flatness"]
theorem mappedQuotient_atPrime
    (I : Ideal R) (q : PrimeSpectrum S)
    (hq : Ideal.map (algebraMap R S) I ≤ q.asIdeal)
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M)))) :
    let Sq := Localization.AtPrime q.asIdeal
    let Mq := LocalizedModule.AtPrime q.asIdeal M
    let IS := Ideal.map (algebraMap R S) I
    let Bbar := S ⧸ IS
    let K := Ideal.map (algebraMap S Sq) IS
    let Tgt := Mq ⧸ (K • (⊤ : Submodule Sq Mq))
    letI : Module (R ⧸ I) Tgt := Module.compHom Tgt (algebraMap (R ⧸ I) Bbar)
    Module.Flat (R ⧸ I) Tgt := by
  intro Sq Mq IS Bbar K Tgt
  let Abar := R ⧸ I
  let Qbar := M ⧸ (IS • (⊤ : Submodule S M))
  let qbar := PrimeSpectrum.quotientOfLE IS q hq
  have hlocalized : Module.Flat Abar (LocalizedModule.AtPrime qbar.asIdeal Qbar) :=
    Module.Flat.localizedModule_of_tower qbar.asIdeal.primeCompl hflat
  letI : Module Abar Tgt := Module.compHom Tgt (algebraMap Abar Bbar)
  letI : IsScalarTower Abar Bbar Tgt := IsScalarTower.of_compHom Abar Bbar Tgt
  let e : LocalizedModule.AtPrime qbar.asIdeal Qbar ≃ₗ[Bbar] Tgt :=
    closedFiberEquiv (R := R) (S := S) (M := M) I q hq
  letI : Module.Flat Abar (LocalizedModule.AtPrime qbar.asIdeal Qbar) := hlocalized
  exact Module.Flat.of_linearEquiv (e.restrictScalars Abar).symm

private lemma localizedSourceIdeal_map_eq
    (I : Ideal R) (q : PrimeSpectrum S) :
    let p := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let J := Ideal.map (algebraMap R Rp) I
    let IS := Ideal.map (algebraMap R S) I
    let K := Ideal.map (algebraMap S Sq) IS
    letI : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
    Ideal.map (algebraMap Rp Sq) J = K := by
  intro p Rp Sq J IS K
  letI : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  calc
    Ideal.map (algebraMap Rp Sq) J = Ideal.map (algebraMap R Sq) I := by
      dsimp [J]
      rw [Ideal.map_map]
      exact congrArg (fun f : R →+* Sq ↦ Ideal.map f I)
        (IsScalarTower.algebraMap_eq R Rp Sq).symm
    _ = K := by
      dsimp [K, IS]
      rw [Ideal.map_map]
      exact congrArg (fun f : R →+* Sq ↦ Ideal.map f I)
        (IsScalarTower.algebraMap_eq R S Sq)

omit [Module R M] [IsScalarTower R S M] in
/-- Flatness of the closed fiber over `R ⧸ I` transfers to the textbook local quotient
`M_q / I R_p M_q` over `R_p / I R_p`.  The source-to-target localization algebra remains local
to the proof, matching Mathlib's non-instance policy for `algebraOfLiesOver`. -/
@[stacks 0523 "localized closed-fiber quotient over the source local ring"]
theorem quotient_atPrime
    (I : Ideal R) (q : PrimeSpectrum S)
    (hq : Ideal.map (algebraMap R S) I ≤ q.asIdeal)
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (Ideal.map (algebraMap R S) I • (⊤ : Submodule S M)))) :
    let p := q.asIdeal.under R
    let Rp := Localization.AtPrime p
    let J := Ideal.map (algebraMap R Rp) I
    let Mq := LocalizedModule.AtPrime q.asIdeal M
    letI : Module Rp Mq :=
      Localization.AtPrime.Relative.algebraMapModule (R := R) q.asIdeal
    Module.Flat (Rp ⧸ J) (Mq ⧸ (J • (⊤ : Submodule Rp Mq))) := by
  intro p Rp J Mq
  let Sq := Localization.AtPrime q.asIdeal
  let IS := Ideal.map (algebraMap R S) I
  let Abar := R ⧸ I
  let Bbar := S ⧸ IS
  let K := Ideal.map (algebraMap S Sq) IS
  let Tgt := Mq ⧸ (K • (⊤ : Submodule Sq Mq))
  letI : Module R M := Module.compHom M (algebraMap R S)
  letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  letI : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  letI : Module Rp Mq :=
    Localization.AtPrime.Relative.algebraMapModule (R := R) q.asIdeal
  letI : IsScalarTower R Rp Mq :=
    Localization.AtPrime.Relative.algebraMapModule_isScalarTower
      (R := R) (S := S) (M := M) q.asIdeal
  letI : IsScalarTower Rp Sq Mq :=
    Localization.AtPrime.Relative.moduleOfLiesOver_isScalarTower
      (M := M) p q.asIdeal
  have hK : Ideal.map (algebraMap Rp Sq) J = K := by
    simpa [p, Rp, Sq, J, IS, K] using
      localizedSourceIdeal_map_eq (R := R) (S := S) I q
  have hJK : J ≤ Ideal.comap (algebraMap Rp Sq) K := by
    rw [← Ideal.map_le_iff_le_comap]
    exact hK.le
  letI : Algebra (Rp ⧸ J) (Sq ⧸ K) :=
    Ideal.Quotient.algebraQuotientOfLEComap hJK
  let quotientModule : Module (Sq ⧸ K) Tgt := inferInstance
  letI : Module (Sq ⧸ K) Tgt := quotientModule
  letI : SMul (Sq ⧸ K) Tgt := quotientModule.toSMul
  let sourceQuotientModule : Module (Rp ⧸ J) Tgt :=
    Module.compHom Tgt (algebraMap (Rp ⧸ J) (Sq ⧸ K))
  letI : Module (Rp ⧸ J) Tgt := sourceQuotientModule
  letI : Module Abar Tgt := Module.compHom Tgt (algebraMap Abar Bbar)
  have hflatAbar : Module.Flat Abar Tgt := by
    simpa [Sq, IS, Abar, Bbar, K, Tgt] using
      mappedQuotient_atPrime (R := R) (S := S) (M := M) I q hq hflat
  have hscalarMap (a : Abar) :
      algebraMap (Rp ⧸ J) (Sq ⧸ K) (algebraMap Abar (Rp ⧸ J) a) =
        algebraMap Bbar (Sq ⧸ K) (algebraMap Abar Bbar a) := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    change Ideal.Quotient.mk K (algebraMap Rp Sq (algebraMap R Rp r)) =
      Ideal.Quotient.mk K (algebraMap S Sq (algebraMap R S r))
    exact congrArg (Ideal.Quotient.mk K) <| by
      change Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
          (algebraMap R Rp r) = algebraMap S Sq (algebraMap R S r)
      exact Localization.localRingHom_to_map p q.asIdeal (algebraMap R S) rfl r
  have hAbarTower : IsScalarTower Abar (Rp ⧸ J) Tgt := by
    refine IsScalarTower.of_algebraMap_smul ?_
    intro a x
    change algebraMap (Rp ⧸ J) (Sq ⧸ K) (algebraMap Abar (Rp ⧸ J) a) • x =
      algebraMap Abar Bbar a • x
    rw [hscalarMap]
    exact IsScalarTower.algebraMap_smul (Sq ⧸ K) (algebraMap Abar Bbar a) x
  letI : IsScalarTower Abar (Rp ⧸ J) Tgt := hAbarTower
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid Abar p.primeCompl) (Rp ⧸ J) :=
    IsLocalization.isLocalization_of_algEquiv _
      (Localization.BaseIdeal.selfAlgEquiv p.primeCompl I Rp)
  have hflatTarget : Module.Flat (Rp ⧸ J) Tgt :=
    (Module.flat_iff_of_isLocalization (Rp ⧸ J)
      (Algebra.algebraMapSubmonoid Abar p.primeCompl) (M := Tgt)).mpr hflatAbar
  have hsourceTower : IsScalarTower Rp (Rp ⧸ J) Tgt := by
    simpa [Tgt] using
      Ideal.Quotient.Map.tower_source_of_le_comap
        (R := Rp) (S := Sq) (M := Mq) J K hJK
  letI : IsScalarTower Rp (Rp ⧸ J) Tgt := hsourceTower
  let mappedDenominator :=
    Ideal.map (algebraMap Rp Sq) J • (⊤ : Submodule Sq Mq)
  have hdenominator : K • (⊤ : Submodule Sq Mq) = mappedDenominator := by
    exact congrArg (fun L : Ideal Sq ↦ L • (⊤ : Submodule Sq Mq)) hK.symm
  let eDenominatorSq : Tgt ≃ₗ[Sq] Mq ⧸ mappedDenominator :=
    Submodule.quotEquivOfEq _ _ hdenominator
  let eDenominator : Tgt ≃ₗ[Rp ⧸ J] Mq ⧸ mappedDenominator :=
    (eDenominatorSq.restrictScalars Rp).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let eMapped : (Mq ⧸ mappedDenominator) ≃ₗ[Rp ⧸ J]
      Mq ⧸ (J • (⊤ : Submodule Rp Mq)) :=
    Ideal.Quotient.Map.smulTopQuotientEquivQuotient
      (R := Rp) (S := Sq) (M := Mq) J
  letI : Module.Flat (Rp ⧸ J) Tgt := hflatTarget
  exact Module.Flat.of_linearEquiv (eDenominator.trans eMapped).symm

end Module.Flat
