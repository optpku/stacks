/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AlgHom.Artinian.PowerRefinement
public import ReasLib.RingTheory.AlgHom.Artinian.Factorisation
public import ReasLib.RingTheory.RingHom.Artinian.PowerRefinement
public import ReasLib.Algebra.CharP.RingHom
public import ReasLib.RingTheory.AlgHom.Local.AtPrime
public import ReasLib.RingTheory.LocalRing.Quotient
public import ReasLib.RingTheory.RingHom.Local.MaximalIdeal
public import ReasLib.RingTheory.RingHom.PowerImage
public import ReasLib.RingTheory.Smooth.EssSmooth
public import ReasLib.FieldTheory.GeometricRegularity
public import Mathlib.RingTheory.RingHom.Flat

@[expose] public section

/-!
# Local Artinian approximation and refinement

The reusable owner API uses bundled primes and algebra homomorphisms.  It
exposes the localized polynomial source and both maximal-ideal-power
quotients as named types, while keeping factorization and locality as
properties of the chosen maps.
-/

open IsLocalRing

universe u v w

namespace Algebra.LocalArtinianApproximation

variable {k : Type u} {A : Type v}

section

variable [CommRing k] [CommRing A] [Algebra k A]

/-- The local polynomial source at the prime induced by `f` and `q`. -/
@[stacks 07FH "localized polynomial source"]
abbrev SourceLocalRing {m : ℕ} (f : MvPolynomial (Fin m) k →ₐ[k] A)
    (q : PrimeSpectrum A) :=
  f.toRingHom.sourceLocalRingAt q

/-- The localization of `A` at `q`. -/
@[stacks 07FH "localized approximation target"]
abbrev TargetLocalRing (q : PrimeSpectrum A) := Localization.AtPrime q.asIdeal

/-- The source local ring modulo the `n`th power of its maximal ideal. -/
@[stacks 07FH "truncated polynomial source"]
abbrev SourceQuotient {m : ℕ} (f : MvPolynomial (Fin m) k →ₐ[k] A)
    (q : PrimeSpectrum A) (n : ℕ) :=
  SourceLocalRing f q ⧸ maximalIdeal (SourceLocalRing f q) ^ n

/-- The target local ring modulo the `n`th power of its maximal ideal. -/
@[stacks 07FH "truncated local target"]
abbrev TargetQuotient (q : PrimeSpectrum A) (n : ℕ) :=
  TargetLocalRing q ⧸ maximalIdeal (TargetLocalRing q) ^ n

/-- The underlying ring map of the localized polynomial algebra map. -/
@[stacks 07FH "localized polynomial approximation ring map"]
noncomputable abbrev localRingHom {m : ℕ} (f : MvPolynomial (Fin m) k →ₐ[k] A)
    (q : PrimeSpectrum A) : SourceLocalRing f q →+* TargetLocalRing q :=
  f.toRingHom.localRingHomAt q

namespace localRingHom

/-- Maximal-ideal preservation for the localized polynomial map is the source
equation `p A_q = q A_q`, with `p = f⁻¹(q)`. -/
@[stacks 07FH "source maximal-ideal equation"]
theorem mapsMaximalIdeal_iff {m : ℕ}
    (f : MvPolynomial (Fin m) k →ₐ[k] A) (q : PrimeSpectrum A) :
    RingHom.MapsMaximalIdeal (localRingHom f q) ↔
      Ideal.map
          ((algebraMap A (TargetLocalRing q)).comp f.toRingHom)
          (Ideal.comap f.toRingHom q.asIdeal) =
        Ideal.map (algebraMap A (TargetLocalRing q)) q.asIdeal := by
  change Ideal.map (localRingHom f q) (maximalIdeal (SourceLocalRing f q)) =
    maximalIdeal (TargetLocalRing q) ↔ _
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      (PrimeSpectrum.comap f.toRingHom q).asIdeal (SourceLocalRing f q),
    ← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal (TargetLocalRing q),
    Ideal.map_map]
  have hmap : (localRingHom f q).comp
      (algebraMap (MvPolynomial (Fin m) k) (SourceLocalRing f q)) =
      (algebraMap A (TargetLocalRing q)).comp f.toRingHom := by
    apply RingHom.ext
    intro x
    exact Localization.localRingHom_to_map
      (PrimeSpectrum.comap f.toRingHom q).asIdeal q.asIdeal f.toRingHom rfl x
  rw [hmap, PrimeSpectrum.comap_asIdeal]

end localRingHom

/-- The quotient of the localized polynomial map as a `k`-algebra homomorphism. -/
@[stacks 07FH "localized polynomial quotient algebra map"]
noncomputable def quotientMap {m n : ℕ}
    (f : MvPolynomial (Fin m) k →ₐ[k] A) (q : PrimeSpectrum A) :
    SourceQuotient f q n →ₐ[k] TargetQuotient q n :=
  Ideal.quotientMapₐ (maximalIdeal (TargetLocalRing q) ^ n) (f.localAlgHomAt q)
    ((IsLocalRing.maximalIdeal_comap (localRingHom f q)).symm ▸
      Ideal.le_comap_pow (f := localRingHom f q)
        (K := maximalIdeal (TargetLocalRing q)) n)

/-- The quotient map sends a class to the class of its localized image. -/
@[stacks 07FH "localized quotient map on classes", simp]
theorem quotientMap_mk {m n : ℕ}
    (f : MvPolynomial (Fin m) k →ₐ[k] A) (q : PrimeSpectrum A)
    (x : SourceLocalRing f q) :
    quotientMap f q (n := n)
        (Ideal.Quotient.mk (maximalIdeal (SourceLocalRing f q) ^ n) x) =
      Ideal.Quotient.mk (maximalIdeal (TargetLocalRing q) ^ n)
        (localRingHom f q x) := rfl

/-- A presentation-specific view of the generic Artinian local factorisation
of the truncated localization map. -/
@[stacks 07FH "local Artinian factorization datum"]
abbrev Factorisation {m : ℕ}
    (f : MvPolynomial (Fin m) k →ₐ[k] A) (q : PrimeSpectrum A) (n : ℕ+) :=
  AlgHom.Factorisation.Artinian.{u, u, v, w} (quotientMap f q (n := n))

end

namespace Factorisation

section

variable [CommRing k] [CommRing A] [Algebra k A]

/-- Build the presentation-specific view from two maps and the generic
Artinian-factorisation properties. -/
noncomputable def ofMaps {m : ℕ} {f : MvPolynomial (Fin m) k →ₐ[k] A}
    {q : PrimeSpectrum A} {n : ℕ+} {D : Type w}
    [CommRing D] [Algebra k D] [IsArtinianRing D] [IsLocalRing D]
    (fromSource : SourceQuotient f q n →ₐ[k] D)
    (toTarget : D →ₐ[k] TargetQuotient q n)
    (factor : toTarget.comp fromSource = quotientMap f q (n := n))
    (smooth : fromSource.toRingHom.EssSmooth)
    (flat : toTarget.toRingHom.Flat) : Factorisation f q n :=
  AlgHom.Factorisation.Artinian.ofMaps fromSource toTarget factor smooth flat

end

section

variable [CommRing k] [CommRing A] [Algebra k A]

/-- The Artinian-local midpoint, factorization, smoothness, and flatness
conditions carried by a local Artinian factorization. -/
@[stacks 07FH "local Artinian factorisation specification"]
theorem spec {m : ℕ}
    {f : MvPolynomial (Fin m) k →ₐ[k] A} {q : PrimeSpectrum A} {n : ℕ+}
    (F : Factorisation f q n) :
    IsArtinianRing F.mid ∧
      IsLocalRing F.mid ∧
      F.toTarget.comp F.fromSource = quotientMap f q (n := n) ∧
      F.fromSource.toRingHom.EssSmooth ∧ F.toTarget.toRingHom.Flat :=
  ⟨inferInstance, inferInstance, F.base.factor, F.smooth, F.flat⟩

end

end Factorisation

section

variable [CommRing A]

/-- The canonical class of an ambient element in the truncated local target. -/
@[stacks 07FI "class in a truncated local target"]
def targetClass (q : PrimeSpectrum A) (n : ℕ) (a : A) : TargetQuotient q n :=
  Ideal.Quotient.mk (maximalIdeal (TargetLocalRing q) ^ n)
    (algebraMap A (TargetLocalRing q) a)

/-- Taking powers commutes with the canonical class in a truncated local
target. -/
@[stacks 07FI "truncated target class powers", simp]
theorem targetClass_pow (q : PrimeSpectrum A) (n e : ℕ) (a : A) :
    targetClass q n (a ^ e) = targetClass q n a ^ e := by
  simp [targetClass]

end

namespace Factorisation

section

variable [CommRing k] [CommRing A] [Algebra k A]

/-- The algebra-compatible power refinement of the target map in a local
Artinian factorisation. -/
@[stacks 07FI "source factorisation power refinement datum"]
abbrev PowerRefinement
    {m : ℕ} {f : MvPolynomial (Fin m) k →ₐ[k] A}
    {q : PrimeSpectrum A} {n : ℕ+}
    (F : Factorisation f q n) (a : A) :=
  AlgHom.Artinian.PowerRefinement.{u, w, v, max w v}
    F.toTarget (targetClass q n a)

namespace PowerRefinement

variable {m : ℕ} {f : MvPolynomial (Fin m) k →ₐ[k] A}
variable {q : PrimeSpectrum A} {n : ℕ+}
variable {F : Factorisation f q n} {a : A}

/-- Refining the intermediate ring preserves the complete quotient
factorisation from the polynomial source to the target. -/
@[stacks 07FI "source factorisation refinement specification"]
theorem sourceFactor (P : PowerRefinement F a) :
    P.toTarget.comp (P.fromSource.comp F.fromSource) =
      quotientMap f q (n := n) := by
  apply AlgHom.ext
  intro x
  exact (DFunLike.congr_fun P.toRingHom.factor (F.fromSource x)).trans
    (DFunLike.congr_fun F.base.factor x)

/-- The defining and derived properties of an algebra-level power refinement. -/
@[stacks 07FI "source factorisation refinement specification"]
theorem spec (P : PowerRefinement F a) :
    IsArtinianRing P.mid ∧
      IsLocalRing P.mid ∧
      IsLocalHom P.fromSource.toRingHom ∧
      IsLocalHom P.toTarget.toRingHom ∧
      P.toTarget.comp P.fromSource = F.toTarget ∧
      P.toTarget.comp (P.fromSource.comp F.fromSource) =
        quotientMap f q (n := n) ∧
      P.fromSource.toRingHom.EssSmooth ∧
      P.toTarget.toRingHom.Flat ∧
      RingHom.PowerImage.InRange P.toTarget.toRingHom
        (targetClass q n a) P.exponent := by
  have hsource : IsLocalHom P.fromSource.toRingHom := by
    apply ((IsLocalRing.local_hom_TFAE _).out 4 0).mp
    exact IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime _)
  have htarget : IsLocalHom P.toTarget.toRingHom := by
    apply ((IsLocalRing.local_hom_TFAE _).out 4 0).mp
    exact IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime _)
  have hfactor : P.toTarget.comp P.fromSource = F.toTarget :=
    AlgHom.ext fun x => DFunLike.congr_fun P.toRingHom.factor x
  exact ⟨inferInstance, inferInstance, hsource, htarget, hfactor, P.sourceFactor,
    P.toRingHom.smooth, P.toRingHom.flat, P.toRingHom.power_mem⟩

end PowerRefinement

end

namespace PowerRefinement

section

variable [Field k] [CommRing A] [Algebra k A]
variable {m : ℕ} {f : MvPolynomial (Fin m) k →ₐ[k] A}
variable {q : PrimeSpectrum A} {n : ℕ+}

/-- Every intermediate factorisation in positive characteristic admits an
algebra-level power refinement for every ambient element. -/
@[stacks 07FI "existence of a source factorisation power refinement"]
theorem nonempty [IsNoetherianRing A]
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (F : Factorisation f q n) (a : A) :
    Nonempty (PowerRefinement F a) := by
  letI : CharP F.mid p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k F.mid) p (Fact.out : p.Prime).ne_zero
  exact AlgHom.Artinian.PowerRefinement.nonempty (p := p)
    F.toTarget F.flat (targetClass q n a)

end

end PowerRefinement

end Factorisation

section

variable [CommRing k] [CommRing A] [Algebra k A]

/-- A polynomial presentation together with the local and truncated Artinian
factorization conditions of Lemma 16.11.2. -/
@[stacks 07FH "polynomial local Artinian factorization"]
structure PolynomialFactorisation (q : PrimeSpectrum A) (n : ℕ+) where
  /-- The number of polynomial variables. -/
  numVars : ℕ
  /-- The polynomial map into the ambient algebra. -/
  map : MvPolynomial (Fin numVars) k →ₐ[k] A
  /-- The induced map on local rings is flat. -/
  flat : (localRingHom map q).Flat
  /-- The induced map sends the source maximal ideal onto the target maximal
  ideal. -/
  mapsMaximalIdeal : RingHom.MapsMaximalIdeal (localRingHom map q)
  /-- The associated factorization through an Artinian local ring. -/
  factorisation : Factorisation.{u, v, w} map q n

namespace PolynomialFactorisation

/-- Build a polynomial local Artinian factorisation from its polynomial map,
local-map properties, and bundled truncated factorisation. -/
def of {q : PrimeSpectrum A} {n : ℕ+} {m : ℕ}
    (map : MvPolynomial (Fin m) k →ₐ[k] A)
    (flat : (localRingHom map q).Flat)
    (mapsMaximalIdeal : RingHom.MapsMaximalIdeal (localRingHom map q))
    (factorisation : Factorisation.{u, v, w} map q n) :
    PolynomialFactorisation (k := k) (A := A) q n where
  numVars := m
  map := map
  flat := flat
  mapsMaximalIdeal := mapsMaximalIdeal
  factorisation := factorisation

/-- The localized polynomial map underlying a polynomial factorisation. -/
noncomputable abbrev localMap {q : PrimeSpectrum A} {n : ℕ+}
    (P : PolynomialFactorisation (k := k) (A := A) q n) :=
  localRingHom P.map q

/-- The intermediate Artinian local algebra of a polynomial factorisation. -/
abbrev mid {q : PrimeSpectrum A} {n : ℕ+}
    (P : PolynomialFactorisation (k := k) (A := A) q n) :=
  P.factorisation.mid

/-- The source map of the truncated polynomial factorisation. -/
noncomputable abbrev fromSource {q : PrimeSpectrum A} {n : ℕ+}
    (P : PolynomialFactorisation (k := k) (A := A) q n) :
    SourceQuotient P.map q n →ₐ[k] P.mid :=
  P.factorisation.fromSource

/-- The target map of the truncated polynomial factorisation. -/
noncomputable abbrev toTarget {q : PrimeSpectrum A} {n : ℕ+}
    (P : PolynomialFactorisation (k := k) (A := A) q n) :
    P.mid →ₐ[k] TargetQuotient q n :=
  P.factorisation.toTarget

/-- A polynomial factorisation captures a finite family when every chosen
target class lies in the range of its target map. -/
@[stacks 07FH "finite-set capture by a polynomial factorisation"]
def Captures {q : PrimeSpectrum A} {n : ℕ+}
    (P : PolynomialFactorisation (k := k) (A := A) q n)
    (E : Finset (TargetQuotient q n)) : Prop :=
  (↑E : Set (TargetQuotient q n)) ⊆ Set.range P.toTarget

/-- A polynomial local Artinian factorisation together with capture of a
specified finite family in the truncated target. -/
@[stacks 07FH "bundled finite-set polynomial factorisation"]
structure Capture (q : PrimeSpectrum A) (n : ℕ+)
    (E : Finset (TargetQuotient q n)) where
  /-- The polynomial local Artinian factorisation. -/
  factorisation : PolynomialFactorisation.{u, v, w} (k := k) (A := A) q n
  /-- Every selected target class is in the range of the target map. -/
  captures : factorisation.Captures E

namespace Capture

/-- Bundle a polynomial factorisation with a proof that it captures the
specified finite family. -/
def of {q : PrimeSpectrum A} {n : ℕ+} {E : Finset (TargetQuotient q n)}
    (P : PolynomialFactorisation.{u, v, w} (k := k) (A := A) q n)
    (hE : P.Captures E) : Capture (k := k) (A := A) q n E where
  factorisation := P
  captures := hE

/-- The local factorisation properties and range condition carried by a
finite-set capture. -/
theorem spec {q : PrimeSpectrum A} {n : ℕ+}
    {E : Finset (TargetQuotient q n)}
    (C : Capture (k := k) (A := A) q n E) :
    C.factorisation.localMap.Flat ∧
      RingHom.MapsMaximalIdeal C.factorisation.localMap ∧
      IsArtinianRing C.factorisation.mid ∧
      IsLocalRing C.factorisation.mid ∧
      C.factorisation.toTarget.comp C.factorisation.fromSource =
        quotientMap C.factorisation.map q (n := n) ∧
      C.factorisation.fromSource.toRingHom.EssSmooth ∧
      C.factorisation.toTarget.toRingHom.Flat ∧
      C.factorisation.Captures E :=
  ⟨C.factorisation.flat, C.factorisation.mapsMaximalIdeal,
    inferInstance, inferInstance, C.factorisation.factorisation.base.factor,
    C.factorisation.factorisation.smooth, C.factorisation.factorisation.flat,
    C.captures⟩

end Capture

/-- The local-map and Artinian factorization properties carried by a
polynomial factorization. -/
@[stacks 07FH "polynomial factorization specification"]
theorem spec {q : PrimeSpectrum A} {n : ℕ+}
    (P : PolynomialFactorisation (k := k) (A := A) q n) :
    P.localMap.Flat ∧
      RingHom.MapsMaximalIdeal P.localMap ∧
      IsArtinianRing P.mid ∧
      IsLocalRing P.mid ∧
      P.toTarget.comp P.fromSource = quotientMap P.map q (n := n) ∧
      P.fromSource.toRingHom.EssSmooth ∧
      P.toTarget.toRingHom.Flat :=
  ⟨P.flat, P.mapsMaximalIdeal, inferInstance, inferInstance,
    P.factorisation.base.factor, P.factorisation.smooth, P.factorisation.flat⟩

end PolynomialFactorisation

end

section

variable [Field k] [CommRing A] [Algebra k A]

namespace PolynomialFactorisation

/-- Lemma 16.11.2: a finite subset of a positive maximal-ideal-power
quotient of a geometrically regular local algebra is captured by a flat
local Artinian factorization from a localized polynomial algebra. -/
@[stacks 07FH]
theorem Capture.nonempty
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra.IsGeometricallyRegular k A]
    [IsNoetherianRing A] (q : PrimeSpectrum A) (n : ℕ+)
    (E : Finset (TargetQuotient q n)) :
    Nonempty (Capture.{u, v, max u v} (k := k) (A := A) q n E) := sorry

end PolynomialFactorisation

end

end Algebra.LocalArtinianApproximation
