/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo
public import ReasLib.RingTheory.Ideal.Principal

import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor vanishing for Beauville-Laszlo glueing pairs

For a Beauville-Laszlo glueing pair, first Tor vanishes on principal-power ideals, on the quotient
by power torsion, and on the cokernel of `M → M_f`.

@stack 0BNZ
@stack 0BP0
@stack 0BP1
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ModuleTor

namespace CategoryTheory.ModuleCat.Tor

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/-- Lemma 15.91.13: for a Beauville-Laszlo glueing pair, the first Tor of `R'` with every
positive principal-power ideal `(f ^ n)` vanishes. -/
@[stacks 0BNZ "Lemma 15.91.13"]
theorem isZero_one_extension_principalPowerIdeal_of_glueingPair
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) (n : ℕ+) :
    IsZero (Tor₁[R](R', principalPowerIdeal f (n : ℕ))) := sorry

/-- Lemma 15.91.14: for a Beauville-Laszlo glueing pair, the first Tor of `R'` with
`R ⧸ R[f^∞]` vanishes. -/
@[stacks 0BP0 "Lemma 15.91.14"]
theorem isZero_one_extension_quotientByPowerTorsion_of_glueingPair
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    IsZero (Tor₁[R](R', R ⧸ Submodule.torsion' R R (Submonoid.powers f))) := sorry

/-- Lemma 15.91.15: for a Beauville-Laszlo glueing pair, the first Tor of `R'` with the
cokernel of `M → M_f` vanishes. -/
@[stacks 0BP1 "Lemma 15.91.15"]
theorem isZero_one_extension_cokernel_toLocalizationAway_of_glueingPair
    (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    IsZero (Tor₁[R](R',
      LocalizedModule.Away f M ⧸
        LinearMap.range (LocalizedModule.mkLinearMap (Submonoid.powers f) M))) := sorry

end CategoryTheory.ModuleCat.Tor
