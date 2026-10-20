/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Square
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import ReasLib.RingTheory.Localization.Away.Iterated.Equiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base Change for Principal Module Localizations

This leaf identifies localization after extension of scalars with extension
of scalars after localization.  The comparison is linear over the target
principal-localization ring, which is the strength needed to base-change
principal-open module gluing data.

@stack 05EQ
-/

@[expose] public section

open CategoryTheory

universe u v

noncomputable section

namespace Localization.Away

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The square formed by a ring homomorphism and the two canonical maps to
the corresponding principal localizations commutes. -/
@[stacks 05EQ "principal-localization base-change square"]
theorem map_comp_algebraMap (φ : R →+* S) (a : R) :
    (algebraMap S (Localization.Away (φ a))).comp φ =
      (Localization.awayMap φ a).comp
        (algebraMap R (Localization.Away a)) := sorry

/-- Restricting a module over `S_(φ a)` first through `S` or first through
`Rₐ` gives canonically isomorphic `R`-modules.  The comparison is the
categorical form of `map_comp_algebraMap`. -/
@[stacks 05EQ "principal-localization restriction-of-scalars square"]
noncomputable def baseChangeRestrictScalarsIso (φ : R →+* S) (a : R)
    (N : ModuleCat.{v} (Localization.Away (φ a))) :
    (ModuleCat.restrictScalars φ).obj
        ((ModuleCat.restrictScalars
          (algebraMap S (Localization.Away (φ a)))).obj N) ≅
      (ModuleCat.restrictScalars
        (algebraMap R (Localization.Away a))).obj
          ((ModuleCat.restrictScalars
            (Localization.awayMap φ a)).obj N) :=
  (ModuleCat.restrictScalarsComp'App φ
      (algebraMap S (Localization.Away (φ a)))
      ((algebraMap S (Localization.Away (φ a))).comp φ)
      rfl N).symm ≪≫
    (ModuleCat.restrictScalarsCongr
      (map_comp_algebraMap φ a)).app N ≪≫
    ModuleCat.restrictScalarsComp'App
      (algebraMap R (Localization.Away a))
      (Localization.awayMap φ a)
      ((Localization.awayMap φ a).comp
        (algebraMap R (Localization.Away a)))
      rfl N

end Localization.Away

namespace ModuleCat.ExtendScalars

variable {R : Type u} [CommRing R]

/-- Extension of scalars from `R` to `Rₐ` is the canonical localization of
the underlying module away from `a`. -/
@[stacks 05EQ "principal module localization as scalar extension"]
noncomputable def awayIso (a : R) (M : ModuleCat.{v} R) :
    (ModuleCat.extendScalars
        (algebraMap R (Localization.Away a))).obj M ≅
      ModuleCat.of (Localization.Away a) (LocalizedModule.Away a M) :=
  tensorIso (R := R) (S := Localization.Away a) M ≪≫
    (LocalizedModule.equivTensorProduct
      (Submonoid.powers a) M).symm.toModuleIso

end ModuleCat.ExtendScalars

namespace LocalizedModule.Away

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Localizing an extended module away from `φ a` is canonically isomorphic,
as an `S_(φ a)`-module, to extending the localization away from `a` along
`Localization.awayMap φ a`. -/
@[stacks 05EQ "principal module localization commutes with base change"]
noncomputable def baseChangeIso (φ : R →+* S) (a : R)
    (M : ModuleCat.{max u v} R) :
    ModuleCat.of (Localization.Away (φ a))
        (LocalizedModule.Away (φ a)
          ((ModuleCat.extendScalars φ).obj M)) ≅
      (ModuleCat.extendScalars (Localization.awayMap φ a)).obj
        (ModuleCat.of (Localization.Away a)
          (LocalizedModule.Away a M)) :=
  (ModuleCat.ExtendScalars.awayIso (φ a)
      ((ModuleCat.extendScalars φ).obj M)).symm ≪≫
    (ModuleCat.extendScalarsCommSq.{u, v}
      (algebraMap S (Localization.Away (φ a)))
      (Localization.awayMap φ a) φ
      (algebraMap R (Localization.Away a))
      (Localization.Away.map_comp_algebraMap φ a)).iso.app M ≪≫
    (ModuleCat.extendScalars (Localization.awayMap φ a)).mapIso
      (ModuleCat.ExtendScalars.awayIso a M)

/-- Localizing an extended module at the literal target product
`φ a * φ b` is canonically isomorphic to extending its source product
localization along `Localization.Away.productMap φ a b`. -/
@[stacks 05EQ "product principal module localization commutes with base change"]
noncomputable def productBaseChangeIso (φ : R →+* S) (a b : R)
    (M : ModuleCat.{max u v} R) :
    ModuleCat.of (Localization.Away (φ a * φ b))
        (LocalizedModule.Away (φ a * φ b)
          ((ModuleCat.extendScalars φ).obj M)) ≅
      (ModuleCat.extendScalars (Localization.Away.productMap φ a b)).obj
        (ModuleCat.of (Localization.Away (a * b))
          (LocalizedModule.Away (a * b) M)) :=
  (ModuleCat.ExtendScalars.awayIso (φ a * φ b)
      ((ModuleCat.extendScalars φ).obj M)).symm ≪≫
    (ModuleCat.extendScalarsCommSq.{u, v}
      (algebraMap S (Localization.Away (φ a * φ b)))
      (Localization.Away.productMap φ a b) φ
      (algebraMap R (Localization.Away (a * b)))
      (Localization.Away.productMap_comp_algebraMap φ a b).symm).iso.app M ≪≫
    (ModuleCat.extendScalars (Localization.Away.productMap φ a b)).mapIso
      (ModuleCat.ExtendScalars.awayIso (a * b) M)

end LocalizedModule.Away
