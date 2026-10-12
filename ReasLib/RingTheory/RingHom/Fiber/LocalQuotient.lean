/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.Fiber.Quotient
public import ReasLib.RingTheory.RingHom.Fiber.Local

@[expose] public section

/-!
# Local quotient presentations of fibers

@stack 00OL

This leaf identifies the local ring of a residue-field fiber at a target
prime with the quotient of the corresponding target localization.  The
localized algebra structure used by the construction is deliberately local:
Mathlib does not register it globally because it creates instance diamonds.
-/

noncomputable section

universe u v

-- The quotient comparison uses the canonical target-to-fiber map, which is
-- defined with the right tensor-product algebra.  Keeping this choice local
-- avoids exporting the corresponding algebra-instance diamond.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra.Fiber

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The closed fiber of the canonical local map
`R_(q ∩ R) → S_q` at a target prime `q`. -/
@[stacks 00OL]
noncomputable def localClosedFiberAt (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] (q : PrimeSpectrum S) : Type _ :=
  -- Local declaration justification (instance diamond): Mathlib keeps this relative
  -- localization algebra explicit because a global instance creates competing paths.
  letI : Algebra (Localization.AtPrime (q.asIdeal.under R))
      (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  (IsLocalRing.maximalIdeal (Localization.AtPrime (q.asIdeal.under R))).Fiber
    (Localization.AtPrime q.asIdeal)

/-- The canonical closed fiber of a relative prime localization is a commutative ring. -/
noncomputable instance localClosedFiberAtCommRing (q : PrimeSpectrum S) :
    CommRing (localClosedFiberAt R S q) := by
  -- Local declaration justification (instance diamond): unfold with the same named relative
  -- localization algebra used by `localClosedFiberAt`.
  letI : Algebra (Localization.AtPrime (q.asIdeal.under R))
      (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  unfold localClosedFiberAt
  infer_instance

/-- The canonical closed fiber of a relative prime localization is local. -/
noncomputable instance localClosedFiberAtIsLocalRing (q : PrimeSpectrum S) :
    IsLocalRing (localClosedFiberAt R S q) := by
  -- Local instance justification (instance diamond): this is Mathlib's canonical relative
  -- localization algebra, kept out of global search to avoid competing localization maps.
  letI : Algebra (Localization.AtPrime (q.asIdeal.under R))
      (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  unfold localClosedFiberAt
  -- Local instance justification (defeq pin): the localness theorem is stated for the canonical
  -- `localRingHom`, which is the algebra map fixed immediately above.
  letI : IsLocalHom
      (algebraMap (Localization.AtPrime (q.asIdeal.under R))
        (Localization.AtPrime q.asIdeal)) := by
    change IsLocalHom
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S)
        Ideal.LiesOver.over)
    infer_instance
  exact Ideal.Fiber.isLocalRing_of_isLocalHom

/-- The canonical closed fiber of a relative prime localization is Noetherian whenever the
target ring is Noetherian. -/
noncomputable instance localClosedFiberAtIsNoetherianRing [IsNoetherianRing S]
    (q : PrimeSpectrum S) :
    IsNoetherianRing (localClosedFiberAt R S q) := by
  -- Local declaration justification (instance diamond): unfold with the named relative
  -- localization algebra, without registering it globally.
  letI : Algebra (Localization.AtPrime (q.asIdeal.under R))
      (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  unfold localClosedFiberAt
  -- Local declaration justification (proof-local derived instance): localization of the
  -- Noetherian target supplies exactly the instance needed by the fiber theorem.
  letI : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal) inferInstance
  exact Ideal.Fiber.isNoetherianRing (IsLocalRing.maximalIdeal
    (Localization.AtPrime (q.asIdeal.under R)))

/-- Localizing `S` at `q` and quotienting by the extension of `q ∩ R`
recovers the local ring of the residue-field fiber at `q`.

The localized algebra structure needed internally is kept local to this
construction, since registering it globally would create the localization
instance diamond deliberately avoided by Mathlib. -/
noncomputable def localQuotientRingEquiv (q : PrimeSpectrum S) :
    ((Localization.AtPrime q.asIdeal) ⧸
      Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) ≃+*
        fiberLocalRingAt R S q := by
  let p : Ideal R := q.asIdeal.under R
  let r : Ideal S :=
    (fiberPrimeAt R S q).asIdeal.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S)
  let hr : r = q.asIdeal :=
    PrimeSpectrum.fiberPrimeAt_comap_asIdeal (R := R) (S := S) q
  -- Local declaration justification (transport data): `hr` transports primality and lying-over
  -- from the source prime `q` to the explicit contraction ideal `r`.
  letI : r.IsPrime := hr.symm ▸ q.2
  letI : r.LiesOver p :=
    hr.symm ▸ Ideal.over_under q.asIdeal
  -- Local declaration justification (instance diamond): the transported lying-over data selects
  -- Mathlib's named relative-localization algebra.
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime r) :=
    Localization.AtPrime.algebraOfLiesOver p r
  let rSpec : PrimeSpectrum S := ⟨r, inferInstance⟩
  let sourceRing : PrimeSpectrum S → Type v := fun t ↦
    (Localization.AtPrime t.asIdeal) ⧸
      Ideal.map (algebraMap R (Localization.AtPrime t.asIdeal)) p
  let localFiberEquiv : sourceRing rSpec ≃+* fiberLocalRingAt R S q :=
    (Ideal.Fiber.localizationAlgEquivQuotient p
      (fiberPrimeAt R S q).asIdeal).toRingEquiv.symm
  let hSpec : rSpec = q :=
    PrimeSpectrum.ext (show r = q.asIdeal from hr)
  exact Eq.mp
    (congrArg (fun t : PrimeSpectrum S ↦ sourceRing t ≃+* fiberLocalRingAt R S q) hSpec)
    localFiberEquiv

/-- The closed fiber of `R_(q ∩ R) → S_q` identifies with the local ring of the residue-field
fiber at `q`. -/
@[stacks 00OL]
noncomputable def localClosedFiberAtRingEquiv (q : PrimeSpectrum S) :
    localClosedFiberAt R S q ≃+* fiberLocalRingAt R S q := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  -- Local declaration justification (derived instance): contraction makes `q` lie over `p`.
  letI : q.asIdeal.LiesOver p.asIdeal := by
    simpa [p] using (Ideal.over_under q.asIdeal)
  -- Local instance justification (instance diamond): Mathlib intentionally keeps this relative
  -- localization algebra out of global search.
  letI : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  let eClosedFiber :
      localClosedFiberAt R S q ≃+*
        (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) :=
    (Ideal.Fiber.maximalQuotientAlgEquiv (R := Rp) (S := Sq)
      (IsLocalRing.maximalIdeal Rp)).symm.toRingEquiv
  let eRewrite :
      (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) ≃+*
        (Sq ⧸ Ideal.map (algebraMap R Sq) p.asIdeal) :=
    Ideal.quotEquivOfEq
      (map_maximalIdeal_eq (R := R) (S := S) p.asIdeal q.asIdeal inferInstance)
  simpa [localClosedFiberAt, p, Rp, Sq] using
    (eClosedFiber.trans eRewrite).trans (localQuotientRingEquiv (R := R) (S := S) q)

/-- The local quotient presentation sends the class of a target element to
its canonical image in the local fiber ring. -/
@[simp]
theorem localQuotientRingEquiv_apply_mk (q : PrimeSpectrum S) (s : S) :
    localQuotientRingEquiv (R := R) (S := S) q
      (Ideal.Quotient.mk
        (Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R))
        (algebraMap S (Localization.AtPrime q.asIdeal) s)) =
      toFiberLocalRingAt R S q s := sorry

end Algebra.Fiber

end
