/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.GlobalFlattening

/-!
# The actual clopen rank locus inside the displayed flattening subscheme

The carrier is the union of images of the explicitly defined affine quotient
charts, tested by the ranks of their actual scalar-extended eta homology.
There is no choice of an open-and-closed subscheme satisfying a desired rank
predicate. Openness/closedness are the fixed-rank law from flat.tex.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.PerfectGraphAtlas

variable {X Y : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
  (hE : RingedSpace.ModuleDerived.IsPerfect E) (p : Y ⟶ X) (D : Y.IdealSheafData)
  [IsEffectiveCartierDivisor D.subschemeι]

variable (i : GoodEtaChart E hE p D)

/-- The actual affine quotient Spec((A/(f))/sum J_n). -/
def etaAffineT : Scheme.{u} := Spec (.of (etaFlatteningRing E hE p D i))

def etaAffineTToChart : etaAffineT E hE p D i ⟶ etaDivisorChart E hE p D i :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (etaTotalIdeal E hE p D i)))

/-- The ideal sheaf of the displayed quotient is the contraction of the
actual quotient-ring ideal under Gamma-Spec, exactly as used to define local T. -/
theorem etaAffineT_kernel :
    (etaLocalIdealSheaf E hE p D i).subschemeι.ker ≤ (etaAffineTToChart E hE p D i).ker := by
  sorry

def etaAffineTToLocal : etaAffineT E hE p D i ⟶ etaLocalT E hE p D i :=
  @AlgebraicGeometry.IsClosedImmersion.lift
    (etaLocalIdealSheaf E hE p D i).subscheme (etaAffineT E hE p D i) (etaDivisorChart E hE p D i)
    (etaLocalIdealSheaf E hE p D i).subschemeι (etaAffineTToChart E hE p D i)
    (AlgebraicGeometry.IsClosedImmersion.instSubschemeι (etaLocalIdealSheaf E hE p D i))
    (etaAffineT_kernel E hE p D i)

def etaAffineTToGlobal : etaAffineT E hE p D i ⟶ globalT E hE p D :=
  etaAffineTToLocal E hE p D i ≫ etaLocalToGlobalT E hE p D i

theorem etaAffineTToLocal_over : etaAffineTToLocal E hE p D i ≫
    (etaLocalIdealSheaf E hE p D i).subschemeι = etaAffineTToChart E hE p D i :=
  @AlgebraicGeometry.IsClosedImmersion.lift_fac
    (etaLocalIdealSheaf E hE p D i).subscheme (etaAffineT E hE p D i) (etaDivisorChart E hE p D i)
    (etaLocalIdealSheaf E hE p D i).subschemeι (etaAffineTToChart E hE p D i)
    (AlgebraicGeometry.IsClosedImmersion.instSubschemeι (etaLocalIdealSheaf E hE p D i))
    (etaAffineT_kernel E hE p D i)

/-- Stalk rank of the actual local eta homology module, using ordinary
localization at the specified prime; no derived Q is selected here. -/
def etaAffineRank (q : etaAffineT E hE p D i) (n : ℤ) : Cardinal.{u} :=
  Module.rank (Localization.AtPrime q.asIdeal)
    (LocalizedModule.AtPrime q.asIdeal ((etaFlattenedComplex E hE p D i).homology n))

/-- The exact rank-sequence locus described in flat.tex13890ff. The existential
quantifiers define a subset, not an output object selected by choice. -/
def globalRankCarrier (ρ : ℤ → Cardinal.{u}) : Set (globalT E hE p D) :=
  {t | ∃ (i : GoodEtaChart E hE p D) (q : etaAffineT E hE p D i),
    etaAffineTToGlobal E hE p D i q = t ∧ ∀ n : ℤ, etaAffineRank E hE p D i q n = ρ n}

/-- The local eta homologies on T are finite locally free and locally bounded.
Their ranks agree on chart overlaps, so the fixed rank-sequence subset is clopen. -/
theorem globalRankCarrier_clopen (ρ : ℤ → Cardinal.{u}) :
    IsClopen (globalRankCarrier E hE p D ρ) := by
  sorry

def globalRankOpen (ρ : ℤ → Cardinal.{u}) : (globalT E hE p D).Opens :=
  ⟨globalRankCarrier E hE p D ρ, (globalRankCarrier_clopen E hE p D ρ).isOpen⟩

/-- The specific T(rho), constructed from its exact rank carrier. -/
def globalTRank (ρ : ℤ → Cardinal.{u}) : Scheme.{u} :=
  (globalRankOpen E hE p D ρ).toScheme

def globalTRankInclusion (ρ : ℤ → Cardinal.{u}) :
    globalTRank E hE p D ρ ⟶ globalT E hE p D :=
  (globalRankOpen E hE p D ρ).ι

instance globalTRankInclusion_open (ρ : ℤ → Cardinal.{u}) :
    IsOpenImmersion (globalTRankInclusion E hE p D ρ) :=
  inferInstanceAs (IsOpenImmersion (globalRankOpen E hE p D ρ).ι)

instance globalTRankInclusion_closed (ρ : ℤ → Cardinal.{u}) :
    IsClosedImmersion (globalTRankInclusion E hE p D ρ) := by
  apply IsClosedImmersion.of_isPreimmersion
  have hr : Set.range (globalTRankInclusion E hE p D ρ) = globalRankCarrier E hE p D ρ := by
    ext t
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro ht
      exact ⟨⟨t, ht⟩, rfl⟩
  exact hr.symm ▸ (globalRankCarrier_clopen E hE p D ρ).isClosed

/-- The vanishing mode's specific rank-zero locus, with no rank input. -/
def globalTVanishing : Scheme.{u} := globalTRank E hE p D (fun _ => 0)

def globalTVanishingInclusion : globalTVanishing E hE p D ⟶ globalT E hE p D :=
  globalTRankInclusion E hE p D (fun _ => 0)

/-- The degree-zero vector-bundle rank profile occurring in the Chern alternative. -/
def degreeZeroRankProfile (r : ℕ) (n : ℤ) : Cardinal.{u} := if n = 0 then r else 0

/-- For Chern degree q, the exact locus is the finite union of profiles 0≤r<q. -/
def globalRankLTCarrier (q : ℕ) : Set (globalT E hE p D) :=
  ⋃ r : Fin q, globalRankCarrier E hE p D (degreeZeroRankProfile r.val)

theorem globalRankLTCarrier_clopen (q : ℕ) : IsClopen (globalRankLTCarrier E hE p D q) :=
  isClopen_iUnion_of_finite fun r : Fin q =>
    globalRankCarrier_clopen E hE p D (degreeZeroRankProfile r.val)

def globalRankLTOpen (q : ℕ) : (globalT E hE p D).Opens :=
  ⟨globalRankLTCarrier E hE p D q, (globalRankLTCarrier_clopen E hE p D q).isOpen⟩

/-- The source's rank-bound choice of T′ is a fixed rank-locus restriction. -/
def globalTRankLT (q : ℕ) : Scheme.{u} := (globalRankLTOpen E hE p D q).toScheme

def globalTRankLTInclusion (q : ℕ) : globalTRankLT E hE p D q ⟶ globalT E hE p D :=
  (globalRankLTOpen E hE p D q).ι

instance globalTRankLTInclusion_open (q : ℕ) :
    IsOpenImmersion (globalTRankLTInclusion E hE p D q) :=
  inferInstanceAs (IsOpenImmersion (globalRankLTOpen E hE p D q).ι)

instance globalTRankLTInclusion_closed (q : ℕ) :
    IsClosedImmersion (globalTRankLTInclusion E hE p D q) := by
  apply IsClosedImmersion.of_isPreimmersion
  have hr : Set.range (globalTRankLTInclusion E hE p D q) = globalRankLTCarrier E hE p D q := by
    ext t
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro ht
      exact ⟨⟨t, ht⟩, rfl⟩
  exact hr.symm ▸ (globalRankLTCarrier_clopen E hE p D q).isClosed

theorem globalRankOpen_carrier (ρ : ℤ → Cardinal.{u}) :
    ((globalRankOpen E hE p D ρ) : Set (globalT E hE p D)) =
      globalRankCarrier E hE p D ρ := rfl

theorem rankPoint_mem (ρ : ℤ → Cardinal.{u}) (q : etaAffineT E hE p D i)
    (hρ : ∀ n : ℤ, etaAffineRank E hE p D i q n = ρ n) :
    etaAffineTToGlobal E hE p D i q ∈ globalRankCarrier E hE p D ρ :=
  ⟨i, q, rfl, hρ⟩

end AlgebraicGeometry.Scheme.PerfectGraphAtlas
