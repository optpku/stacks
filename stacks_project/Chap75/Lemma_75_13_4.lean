/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import stacks_project.Chap59.Lemma_59_40_1_Hom
public import stacks_project.Chap75.Lemma_75_13_4_Relative
public import stacks_project.Chap75.Lemma_75_13_4_Sites

/-!
# Lemma 75.13.4

Tor-amplitude in a fixed interval, and locally finite Tor dimension, of a
derived `𝒪_X`-module as an object of `D(f⁻¹𝒪_Y)` may equivalently be tested
after exact pullback along the commutative presentation of ε from 75.4.0.1.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.SiteRestriction
open CategoryTheory
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived
open Scheme.Etale.Small

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

variable {X Y : Scheme.{u}}

/-- Lemma 75.13.4 (1): for a morphism of schemes `f : X ⟶ Y` and `E` in
`D(𝒪_X)`, `E` has tor amplitude in `[a, b]` as an object of `D(f⁻¹𝒪_Y)` if and
only if `ε* E` has tor amplitude in `[a, b]` as an object of
`D(f_small⁻¹𝒪_{Y_étale})`, where `ε` is `commSmallEtaleToZariski` as in
75.4.0.1. -/
@[stacks 0DK7]
theorem hasTorAmplitudeInOver_iff (f : X ⟶ Y)
    (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) (a b : ℤ) :
    HasTorAmplitudeInOver (zariskiCommRingedHom f) E a b ↔
      HasTorAmplitudeInOver (commRingedHom f)
        ((IsFlat.exactPullback (commSmallEtaleToZariski X)).mapDerivedCategory.obj
          E) a b :=
  sorry

/-- Lemma 75.13.4 (2): for a morphism of schemes `f : X ⟶ Y` and `E` in
`D(𝒪_X)`, `E` locally has finite tor dimension as an object of `D(f⁻¹𝒪_Y)` if
and only if `ε* E` locally has finite tor dimension as an object of
`D(f_small⁻¹𝒪_{Y_étale})`, where `ε` is `commSmallEtaleToZariski` as in
75.4.0.1. -/
@[stacks 0DK7]
theorem locallyHasFiniteTorDimensionOver_iff (f : X ⟶ Y)
    (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) :
    LocallyHasFiniteTorDimensionOver (zariskiCommRingedHom f) E ↔
      LocallyHasFiniteTorDimensionOver (commRingedHom f)
        ((IsFlat.exactPullback (commSmallEtaleToZariski X)).mapDerivedCategory.obj
          E) :=
  sorry

end AlgebraicGeometry.Scheme.SiteRestriction
