/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.UniversallyInjective
public import ReasLib.LinearAlgebra.UniversallyInjective.Localization.Relative
public import ReasLib.RingTheory.Localization.Map

/-!
# Localization of universally injective linear maps

This file records the stability and comparison statements for tensor-stable injectivity under
localization and restriction of scalars.

@stack 05CM
-/

@[expose] public section

universe u v w x z

namespace LinearMap.UniversallyInjective.Localization

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]
variable {S : Submonoid A} {S' : Submonoid B}

variable {M : Type w} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
variable {M' : Type x} [AddCommGroup M'] [Module A M'] [Module B M'] [IsScalarTower A B M']

/-- The universally injective predicate for the localized map, with the selected algebra map
`Localization.mapAlgebra` and its canonical restricted module structures in scope. -/
@[stacks 05CM "localized universally injective map predicate"]
noncomputable def mapOverLocalization
    [Fact (S ≤ S'.comap (algebraMap A B))] (f : M →ₗ[B] M') : Prop :=
  -- Local instance justification (instance diamond): `Localization.mapAlgebra` is deliberately a
  -- named construction in Mathlib; the module and tower structures below are its restrictions.
  letI : Algebra (Localization S) (Localization S') := Localization.mapAlgebra Fact.out
  letI : Module (Localization S) (LocalizedModule S' M) :=
    Module.restrictScalars (Localization S) (Localization S') (LocalizedModule S' M)
  letI : Module (Localization S) (LocalizedModule S' M') :=
    Module.restrictScalars (Localization S) (Localization S') (LocalizedModule S' M')
  letI : IsScalarTower (Localization S) (Localization S') (LocalizedModule S' M) :=
    IsScalarTower.restrictScalars (Localization S) (Localization S') (LocalizedModule S' M)
  letI : IsScalarTower (Localization S) (Localization S') (LocalizedModule S' M') :=
    IsScalarTower.restrictScalars (Localization S) (Localization S') (LocalizedModule S' M')
  UniversallyInjective.{u, max v w, max v x, z}
    ((LocalizedModule.map S' f).restrictScalars (Localization S))

/-- Lemma 10.82.12 (1a): localizing a `B`-linear map that is universally injective over `A`
again yields a map universally injective over `A`. -/
@[stacks 05CM "universal injectivity after restriction of scalars and localization"]
theorem map_restrictScalars
    (f : M →ₗ[B] M')
    (hf : UniversallyInjective.{u, w, x, z} (f.restrictScalars A)) :
    UniversallyInjective.{u, max v w, max v x, z}
      ((LocalizedModule.map S' f).restrictScalars A) := sorry

section

variable [Fact (S ≤ S'.comap (algebraMap A B))]

/-- Lemma 10.82.12 (1b): after localizing `A` at `S` and `B` at `S'`, the localized map of an
`A`-universally injective `B`-linear map is universally injective over `Localization S`. -/
@[stacks 05CM "universal injectivity after compatible localization"]
theorem map_overLocalization
    (f : M →ₗ[B] M')
    (hf : UniversallyInjective.{u, w, x, z} (f.restrictScalars A)) :
    mapOverLocalization (S := S) (S' := S') f := sorry

variable {N : Type w} [AddCommGroup N] [Module (Localization S') N]
variable {N' : Type x} [AddCommGroup N'] [Module (Localization S') N']

/-- Universal injectivity over the base localization for a map of `Localization S'`-modules.

The selected map algebra and the derived restricted module/tower structures are kept inside the
predicate, so callers can use one semantic object instead of rebuilding them locally. -/
@[stacks 05CM "base-localized universally injective map predicate"]
noncomputable def overLocalization (f : N →ₗ[Localization S'] N') : Prop :=
  -- Local instance justification (instance diamond): the named map algebra is canonical for this
  -- predicate, but registering all localization towers globally would introduce diamonds.
  letI : Algebra (Localization S) (Localization S') := Localization.mapAlgebra Fact.out
  LinearMap.UniversallyInjective.overBase.{u, v, w, x, z}
    (R := Localization S) (A := Localization S') f

/-- Lemma 10.82.12 (2): for maps of `Localization S'`-modules, universal injectivity over `A`
is equivalent to universal injectivity over `Localization S`. -/
@[stacks 05CM "universal injectivity over the base versus localized ring"]
theorem overLocalization_iff
    (f : N →ₗ[Localization S'] N') :
    LinearMap.UniversallyInjective.overBase (R := A) (A := Localization S') f ↔
      overLocalization (S := S) (S' := S') f := sorry

end

end LinearMap.UniversallyInjective.Localization
