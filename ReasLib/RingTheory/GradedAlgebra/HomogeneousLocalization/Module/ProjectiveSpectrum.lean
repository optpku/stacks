module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Away.Module
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Module.Basic

/-!
# Graded modules on projective-spectrum charts

This leaf owns the comparison from the degree-zero localization of a graded
module on a basic open to its localization at a point of that open.  The
selected scalar structures are named data because the denominator inclusion
is not a canonical global algebra action.

@stack 00JR
-/

@[expose] public section

open AlgebraicGeometry ProjectiveSpectrum LocalizedModule HomogeneousLocalization

universe u v w

namespace HomogeneousLocalization.Module

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M]
variable (𝒜 : ℕ → Submodule R S) (ℳ : ℕ → Submodule R M)
variable [GradedAlgebra 𝒜] [SetLike.GradedSMul 𝒜 ℳ]

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- The algebra structure induced by enlarging denominators from powers of `f`
to the complement of the homogeneous prime represented by `x`. -/
@[stacks 00JR "basic-open to homogeneous-prime algebra", implicit_reducible]
noncomputable def awayAtPrimeAlgebra {d : ℕ} (f : 𝒜 d)
    (x : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : S)) :
    Algebra (Away 𝒜 (f : S))
      (HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
  (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra

-- Local declaration justification (selected denominator map): all following declarations use
-- this named action; registering it globally would compete with other homogeneous-localization
-- actions.
attribute [local instance] awayAtPrimeAlgebra

/-- The corresponding action of the basic-open ring on the ordinary module
localization at `x`. -/
@[stacks 00JR "basic-open action on the module localization at a point", implicit_reducible]
noncomputable def awayAtPrimeModule {d : ℕ} (f : 𝒜 d)
    (x : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : S)) :
    Module (Away 𝒜 (f : S))
      (LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl M) :=
  Module.compHom (LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl M)
    (algebraMap (Away 𝒜 (f : S))
      (HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal))

attribute [local instance] awayAtPrimeModule

/-- The selected basic-open, homogeneous-prime, and module-localization
actions form a scalar tower. -/
@[stacks 00JR "basic-open module-localization scalar tower"]
theorem awayAtPrimeTower {d : ℕ} (f : 𝒜 d)
    (x : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : S)) :
    IsScalarTower (Away 𝒜 (f : S))
      (HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)
      (LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl M) := sorry

attribute [local instance] awayAtPrimeTower

/-- Enlarging denominators from powers of `f` to the prime complement is
linear over the degree-zero localization away from `f`. -/
theorem liftOfLE_map_smul {d : ℕ} (f : 𝒜 d)
    (x : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : S)) (r : Away 𝒜 (f : S))
    (z : LocalizedModule.Away (f : S) M) :
    LocalizedModule.liftOfLE (Submonoid.powers (f : S))
        x.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr x.2) (r • z) =
      r • LocalizedModule.liftOfLE (Submonoid.powers (f : S))
        x.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr x.2) z := sorry

/-- The ambient linear comparison obtained by enlarging the denominator
submonoid. -/
@[stacks 00JR "ambient module map from a basic open to a point"]
noncomputable def awayToAtPrimeAmbient {d : ℕ} (f : 𝒜 d)
    (x : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : S)) :
    LocalizedModule.Away (f : S) M →ₗ[Away 𝒜 (f : S)]
      LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl M := sorry

/-- The ambient comparison preserves the degree-zero parts. -/
theorem awayToAtPrimeAmbient_mem_degreeZeroPart {d : ℕ} (f : 𝒜 d)
    (x : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : S))
    {z : LocalizedModule.Away (f : S) M}
    (hz : z ∈ Away.Module.degreeZeroPart 𝒜 ℳ f) :
    awayToAtPrimeAmbient 𝒜 f x z ∈
      degreeZeroPart 𝒜 ℳ x.1.asHomogeneousIdeal.toIdeal.primeCompl := sorry

/-- The explicit comparison `M_(f) → M_(x)` between degree-zero homogeneous
localizations. -/
@[stacks 00JR "graded-module basic-open to point comparison"]
noncomputable def awayToAtPrime {d : ℕ} (f : 𝒜 d)
    (x : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : S)) :
    Away.Module.degreeZeroPart 𝒜 ℳ f →ₗ[Away 𝒜 (f : S)]
      (degreeZeroPart 𝒜 ℳ x.1.asHomogeneousIdeal.toIdeal.primeCompl).restrictScalars
        (Away 𝒜 (f : S)) := sorry

/-- On ordinary localized modules, `awayToAtPrime` is denominator
enlargement. -/
@[stacks 00JR "graded-module comparison on underlying fractions"]
theorem awayToAtPrime_apply {d : ℕ} (f : 𝒜 d)
    (x : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : S))
    (z : Away.Module.degreeZeroPart 𝒜 ℳ f) :
    ((awayToAtPrime 𝒜 ℳ f x z :
        (degreeZeroPart 𝒜 ℳ x.1.asHomogeneousIdeal.toIdeal.primeCompl).restrictScalars
          (Away 𝒜 (f : S))) :
      LocalizedModule x.1.asHomogeneousIdeal.toIdeal.primeCompl M) =
      LocalizedModule.liftOfLE (Submonoid.powers (f : S))
        x.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr x.2) z := sorry

/-- Lemma 10.57.5 (2): for a positive-degree homogeneous `f` and
`x ∈ D₊(f)`, the comparison `M_(f) → M_(x)` is localization at the
corresponding prime of `Spec(S_(f))`. -/
@[stacks 00JR]
theorem awayToAtPrime_isLocalizedModule {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (x : AlgebraicGeometry.Proj.basicOpen 𝒜 (f : S)) :
    IsLocalizedModule
      (((ProjectiveSpectrum.Proj.toSpec 𝒜 (f : S)).base x).asIdeal.primeCompl)
      (awayToAtPrime 𝒜 ℳ f x) := sorry

end HomogeneousLocalization.Module
