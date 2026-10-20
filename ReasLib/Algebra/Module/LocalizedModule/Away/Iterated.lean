/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Localization.Away.Iterated

/-!
# Iterated Principal Localizations of Modules

The second localization of `LocalizedModule.Away a M` is over
`Localization.Away a`, not over `R`. Accordingly, `Iterated a b M` localizes
`LocalizedModule.Away a M` away from the image of `b` in `Localization.Away a`.

`Localization.Away.Iterated.rightAlgebra` supplies the canonical ring action
from `Localization.Away a` to `Localization.Away (a * b)`. It is deliberately
not global, since another ambient algebra action may have the same endpoints.
This file similarly keeps the induced module action named rather than global,
and requires explicit scalar-tower and unit certificates for concrete module
comparisons. No concrete definition here depends on project proof debt.
-/

@[expose] public section

universe u v w

namespace LocalizedModule.Away

variable {R : Type u} [CommSemiring R]

/-- Tag `051T`: the correctly based iterated principal localization of an
`R`-module. Its second denominator is the image of `b` in
`Localization.Away a`. -/
@[stacks 051T "iterated principal localized module"]
abbrev Iterated
    (a b : R) (M : Type v) [AddCommMonoid M] [Module R M] : Type max u v :=
  LocalizedModule.Away (Localization.Away.Iterated.coefficient a b)
    (LocalizedModule.Away a M)

namespace Iterated

/-- Tag `051T`: the condition that the second-stage principal denominators
act invertibly on a `Localization.Away a`-module. -/
@[stacks 051T "iterated principal localized module unit criterion"]
def IsUnitOn
    (a b : R) (P : Type w) [AddCommMonoid P] [Module (Localization.Away a) P] : Prop :=
  ∀ s : Submonoid.powers (Localization.Away.Iterated.coefficient a b),
    IsUnit (algebraMap (Localization.Away a) (Module.End (Localization.Away a) P) s)

/-- Tag `051T`: the `Localization.Away a`-module structure on
`LocalizedModule.Away (a * b) M` induced by the canonical right-handed
principal-localization algebra action. It is named rather than global because
the same carrier can support a different ambient module action. -/
@[stacks 051T "iterated principal localized module right action"]
noncomputable abbrev rightModule
    (a b : R) (M : Type v) [AddCommMonoid M] [Module R M] :
    Module (Localization.Away a) (LocalizedModule.Away (a * b) M) :=
  Module.compHom _
    (IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (a * b)) a b)

/-- Tag `051T`: the named right-handed module action on
`LocalizedModule.Away (a * b) M` is compatible with its existing `R`-module
structure. This theorem is a certificate companion and is not used to build
concrete comparison data. -/
@[stacks 051T "iterated principal localized module right scalar tower"]
theorem rightModule_isScalarTower
    (a b : R) (M : Type v) [AddCommMonoid M] [Module R M] :
    letI : Module (Localization.Away a) (LocalizedModule.Away (a * b) M) :=
      rightModule a b M
    IsScalarTower R (Localization.Away a) (LocalizedModule.Away (a * b) M) := sorry

/-- Tag `051T`: under `rightModule a b M`, the image of `b` and all of its
powers act invertibly on `LocalizedModule.Away (a * b) M`. This is a
certificate companion for `toMulOfUnits`, not an input to its concrete data. -/
@[stacks 051T "iterated principal localized module right unit criterion"]
theorem rightModule_isUnitOn
    (a b : R) (M : Type v) [AddCommMonoid M] [Module R M] :
    letI : Module (Localization.Away a) (LocalizedModule.Away (a * b) M) :=
      rightModule a b M
    IsUnitOn a b (LocalizedModule.Away (a * b) M) := sorry

/-- Tag `051T`: the second canonical localization map from
`LocalizedModule.Away a M` to its localization away from the image of `b`. -/
@[stacks 051T "iterated principal localized module generator"]
noncomputable def mk
    (a b : R) (M : Type v) [AddCommMonoid M] [Module R M] :
    LocalizedModule.Away a M →ₗ[Localization.Away a] Iterated a b M :=
  LocalizedModule.mkLinearMap
    (Submonoid.powers (Localization.Away.Iterated.coefficient a b))
    (LocalizedModule.Away a M)

/-- Tag `051T`: the universal map out of a correctly based iterated principal
localization. The `Localization.Away a`-action and scalar tower on `P` are
explicit because they are mathematical input, rather than globally canonical
instances. -/
@[stacks 051T "iterated principal localized module lift"]
noncomputable def lift
    (a b : R) {M : Type v} [AddCommMonoid M] [Module R M]
    {P : Type w} [AddCommMonoid P] [Module R P]
    [Module (Localization.Away a) P] [IsScalarTower R (Localization.Away a) P]
    (g : M →ₗ[R] P) (h_units : IsUnitOn a b P) :
    Iterated a b M →ₗ[Localization.Away a] P :=
  LocalizedModule.lift
    (Submonoid.powers (Localization.Away.Iterated.coefficient a b))
    ((LocalizedModule.isBaseChange (Submonoid.powers a) M).lift g) h_units

/-- The universal iterated-localization map agrees on a second-stage
canonical generator with the scalar extension of its original map. -/
@[simp, stacks 051T "iterated principal localized module lift application"]
theorem lift_apply_mk
    (a b : R) {M : Type v} [AddCommMonoid M] [Module R M]
    {P : Type w} [AddCommMonoid P] [Module R P]
    [Module (Localization.Away a) P] [IsScalarTower R (Localization.Away a) P]
    (g : M →ₗ[R] P) (h_units : IsUnitOn a b P) (x : LocalizedModule.Away a M) :
    lift a b g h_units (mk a b M x) =
      (LocalizedModule.isBaseChange (Submonoid.powers a) M).lift g x := sorry

/-- Tag `051T`: a comparison from the correctly based iterated principal
localization to `LocalizedModule.Away (a * b) M`, under a supplied
`Localization.Away a`-module action and second-stage unit criterion. The
intended named action is `rightModule a b M`; a zero-input canonical comparison
must wait for the corresponding certificates to be proved. -/
@[stacks 051T "iterated principal localized module product comparison"]
noncomputable def toMulOfUnits
    (a b : R) {M : Type v} [AddCommMonoid M] [Module R M]
    [Module (Localization.Away a) (LocalizedModule.Away (a * b) M)]
    [IsScalarTower R (Localization.Away a) (LocalizedModule.Away (a * b) M)]
    (h_units : IsUnitOn a b (LocalizedModule.Away (a * b) M)) :
    Iterated a b M →ₗ[Localization.Away a] LocalizedModule.Away (a * b) M :=
  lift a b (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M) h_units

/-- The supplied-unit product comparison sends the canonical iterated image of
an original module element to its canonical image in
`LocalizedModule.Away (a * b) M`. -/
@[simp, stacks 051T "iterated principal localized module product comparison application"]
theorem toMulOfUnits_apply_mk
    (a b : R) {M : Type v} [AddCommMonoid M] [Module R M]
    [Module (Localization.Away a) (LocalizedModule.Away (a * b) M)]
    [IsScalarTower R (Localization.Away a) (LocalizedModule.Away (a * b) M)]
    (h_units : IsUnitOn a b (LocalizedModule.Away (a * b) M)) (m : M) :
    toMulOfUnits a b h_units
        (mk a b M (LocalizedModule.mkLinearMap (Submonoid.powers a) M m)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M m := sorry

/-- Tag `051T`: a supplied bijectivity certificate upgrades the supplied-unit
product comparison to a linear equivalence. The certificates remain explicit
so the equivalence data never depends on an unfinished project theorem. -/
@[stacks 051T "iterated principal localized module product equivalence"]
noncomputable def toMulEquiv
    (a b : R) {M : Type v} [AddCommMonoid M] [Module R M]
    [Module (Localization.Away a) (LocalizedModule.Away (a * b) M)]
    [IsScalarTower R (Localization.Away a) (LocalizedModule.Away (a * b) M)]
    (h_units : IsUnitOn a b (LocalizedModule.Away (a * b) M))
    (h_bijective : Function.Bijective (toMulOfUnits a b h_units)) :
    Iterated a b M ≃ₗ[Localization.Away a] LocalizedModule.Away (a * b) M :=
  LinearEquiv.ofBijective (toMulOfUnits a b h_units) h_bijective

/-- The forward linear map of `toMulEquiv` is the supplied-unit
comparison from which it is constructed. -/
@[simp, stacks 051T "iterated principal localized module product equivalence map"]
theorem toMulEquiv_toLinearMap
    (a b : R) {M : Type v} [AddCommMonoid M] [Module R M]
    [Module (Localization.Away a) (LocalizedModule.Away (a * b) M)]
    [IsScalarTower R (Localization.Away a) (LocalizedModule.Away (a * b) M)]
    (h_units : IsUnitOn a b (LocalizedModule.Away (a * b) M))
    (h_bijective : Function.Bijective (toMulOfUnits a b h_units)) :
    (toMulEquiv a b h_units h_bijective).toLinearMap =
      toMulOfUnits a b h_units := sorry

/-- The supplied-unit product equivalence sends a canonical iterated image to
the corresponding canonical image in `LocalizedModule.Away (a * b) M`. -/
@[simp, stacks 051T "iterated principal localized module product equivalence application"]
theorem toMulEquiv_apply_mk
    (a b : R) {M : Type v} [AddCommMonoid M] [Module R M]
    [Module (Localization.Away a) (LocalizedModule.Away (a * b) M)]
    [IsScalarTower R (Localization.Away a) (LocalizedModule.Away (a * b) M)]
    (h_units : IsUnitOn a b (LocalizedModule.Away (a * b) M))
    (h_bijective : Function.Bijective (toMulOfUnits a b h_units)) (m : M) :
    toMulEquiv a b h_units h_bijective
        (mk a b M (LocalizedModule.mkLinearMap (Submonoid.powers a) M m)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M m := sorry

end Iterated

end LocalizedModule.Away
