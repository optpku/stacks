/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.Single
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-zero data for single-principal-open formal gluing

The single pullback object has a canonical Cech differential.  This leaf owns
its concrete localized-side map, kernel module, and kernel short complex; the
surjectivity/exactness theorem is intentionally a separate propositional
bridge.

@stack 0BP3
@stack 0BP4
@stack 0BP5
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open LocalizedModule (Away mkLinearMap equivTensorProduct)
open scoped CategoricalPullback TensorProduct

universe u

noncomputable section

namespace LocalizedModule.Away.FormalGluing.Single

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The single-element module pullback target for `φ` and `f`. -/
@[stacks 0BP3 "single-principal-open module pullback"]
abbrev Pullback (φ : R →+* S) (f : R) :=
  CategoricalPullback
    (ModuleCat.extendScalars (algebraMap S (Localization.Away (φ f))))
    (ModuleCat.extendScalars (overlapMap φ f))

/-- The target-ring localization of the global component of a pullback datum. -/
noncomputable abbrev localizedGlobal (φ : R →+* S) (f : R)
    (X : Pullback φ f) : ModuleCat (Localization.Away (φ f)) :=
  ModuleCat.of (Localization.Away (φ f))
    (Away (φ f) X.fst)

/- The actions below are canonical consequences of the displayed ring maps.  They
are owned here so chapter specializations do not rebuild proof-local `letI`s. -/
/-- The global component carries its canonical `R`-module structure. -/
@[stacks 0BP3 "base-ring action on the global gluing component"]
instance globalModule (φ : R →+* S) (f : R) (X : Pullback φ f) :
    Module R ↑X.fst :=
  Module.compHom _ φ

/-- The localized component carries the `R`-action induced by `Localization.Away f`. -/
@[stacks 0BP3 "base-ring action on the localized gluing component"]
instance localModule (φ : R →+* S) (f : R) (X : Pullback φ f) :
    Module R ↑X.snd :=
  Module.compHom _ (algebraMap R (Localization.Away f))

/-- The localized component has the canonical `R`-`Localization.Away f` scalar tower. -/
@[stacks 0BP3 "scalar tower on the localized gluing component"]
instance localTower (φ : R →+* S) (f : R) (X : Pullback φ f) :
    IsScalarTower R (Localization.Away f) ↑X.snd :=
  IsScalarTower.of_compHom R (Localization.Away f) ↑X.snd

/-- The overlap localization has its canonical algebra over `Localization.Away f`. -/
@[stacks 0BP3 "algebra structure on the overlap localization"]
instance overlapAlgebra (φ : R →+* S) (f : R) :
    Algebra (Localization.Away f) (Localization.Away (φ f)) :=
  (overlapMap φ f).toAlgebra

/-- The localized global component carries the canonical base-ring action. -/
@[stacks 0BP3 "base-ring action on the localized global component"]
instance localizedGlobalModule (φ : R →+* S) (f : R) (X : Pullback φ f) :
    Module R (Away (φ f) ↑X.fst) :=
  Module.compHom _ (baseToOverlap φ f)

/-- The global component viewed as an `R`-module. -/
abbrev global (φ : R →+* S) (f : R) (X : Pullback φ f) : ModuleCat R :=
  ModuleCat.of R ↑X.fst

/-- The localized component viewed as an `R`-module. -/
abbrev localModuleCat (φ : R →+* S) (f : R) (X : Pullback φ f) : ModuleCat R :=
  ModuleCat.of R ↑X.snd

/-- The localized global component viewed as an `R`-module. -/
abbrev localizedGlobalR (φ : R →+* S) (f : R) (X : Pullback φ f) : ModuleCat R :=
  ModuleCat.of R (Away (φ f) ↑X.fst)

/-- The scalar tower on the restricted copy of the overlap ring. -/
@[stacks 0BP3 "scalar tower on the restricted overlap ring"]
instance overlapSelfIsScalarTower (φ : R →+* S) (f : R) :
    IsScalarTower S (Localization.Away (φ f))
      ↑((ModuleCat.restrictScalars
        (algebraMap S (Localization.Away (φ f)))).obj
          (ModuleCat.of (Localization.Away (φ f)) (Localization.Away (φ f)))) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- The scalar tower on the restricted copy of the overlap ring along
`Localization.awayMap φ f`. -/
@[stacks 0BP3 "source-localized scalar tower on the overlap ring"]
instance sideOverlapSelfIsScalarTower (φ : R →+* S) (f : R) :
    IsScalarTower (Localization.Away f) (Localization.Away (φ f))
      ↑((ModuleCat.restrictScalars (overlapMap φ f)).obj
          (ModuleCat.of (Localization.Away (φ f)) (Localization.Away (φ f)))) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- The canonical scalar normalization from the restricted overlap copy to
the literal overlap ring. -/
noncomputable def overlapSelfEquiv (φ : R →+* S) (f : R) :
    ↑((ModuleCat.restrictScalars
      (algebraMap S (Localization.Away (φ f)))).obj
        (ModuleCat.of (Localization.Away (φ f)) (Localization.Away (φ f)))) ≃ₗ[
          Localization.Away (φ f)] Localization.Away (φ f) :=
  { __ := AddEquiv.refl _
    map_smul' := fun _ _ ↦ rfl }

/-- The scalar normalization along the source-to-overlap localization map. -/
noncomputable def sideOverlapSelfEquiv (φ : R →+* S) (f : R) :
    ↑((ModuleCat.restrictScalars (overlapMap φ f)).obj
      (ModuleCat.of (Localization.Away (φ f)) (Localization.Away (φ f)))) ≃ₗ[
        Localization.Away (φ f)] Localization.Away (φ f) :=
  { __ := AddEquiv.refl _
    map_smul' := fun _ _ ↦ rfl }

/-- The canonical tensor presentation of the global component over the overlap. -/
noncomputable def extendToOverlapIso (φ : R →+* S) (f : R)
    (X : Pullback φ f) :
    (ModuleCat.extendScalars (algebraMap S (Localization.Away (φ f)))).obj X.fst ≅
      ModuleCat.of (Localization.Away (φ f))
        (Localization.Away (φ f) ⊗[S] X.fst) :=
  (TensorProduct.AlgebraTensorModule.congr
    (overlapSelfEquiv φ f)
    (LinearEquiv.refl S ↑X.fst)).toModuleIso

/-- The overlap tensor-to-localization comparison. -/
noncomputable abbrev overlapTensorToAway (φ : R →+* S) (f : R)
    (X : Pullback φ f) :
    Localization.Away (φ f) ⊗[S] ↑X.fst →ₗ[Localization.Away (φ f)]
      Away (φ f) ↑X.fst :=
  (equivTensorProduct (Submonoid.powers (φ f)) ↑X.fst).symm

/-- The localized-side component transported into the localized global module. -/
@[stacks 0BP3 "single-principal-open localized-side map"]
noncomputable def localizedSideMap (φ : R →+* S) (f : R)
    (X : Pullback φ f) :
    ↑(localModuleCat φ f X) →ₗ[R] ↑(localizedGlobalR φ f X) :=
  let overlap : ModuleCat (Localization.Away (φ f)) := localizedGlobal φ f X
  let tensorToAway :
      (ModuleCat.extendScalars (algebraMap S (Localization.Away (φ f)))).obj X.fst ⟶ overlap :=
    (extendToOverlapIso φ f X).hom ≫
      ModuleCat.ofHom (overlapTensorToAway φ f X)
  let sideMap : X.snd ⟶ (ModuleCat.restrictScalars (overlapMap φ f)).obj overlap :=
    ((ModuleCat.extendRestrictScalarsAdj (overlapMap φ f)).homEquiv X.snd overlap)
      (X.iso.inv ≫ tensorToAway)
  let mapR : (localModuleCat φ f X) ⟶ (localizedGlobalR φ f X) :=
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away f))).map sideMap ≫
      ((ModuleCat.restrictScalarsComp'
        (algebraMap R (Localization.Away f))
        (overlapMap φ f)
        (baseToOverlap φ f)
        (square_comm φ f)).symm.app overlap).hom
  ModuleCat.Hom.hom mapR

/- The localization map is S-linear by construction; the following two laws
record its explicit R-linear view against `baseToOverlap`. -/
/-- Additivity of the base-ring view of the global localization map. -/
theorem globalLocalizationMap_add (φ : R →+* S) (f : R) (X : Pullback φ f)
    (x y : ↑X.fst) :
    (mkLinearMap (Submonoid.powers (φ f)) ↑X.fst) (x + y) =
      (mkLinearMap (Submonoid.powers (φ f)) ↑X.fst) x +
        (mkLinearMap (Submonoid.powers (φ f)) ↑X.fst) y := sorry

/-- Compatibility with base scalars of the global localization map. -/
theorem globalLocalizationMap_smul (φ : R →+* S) (f : R) (X : Pullback φ f)
    (r : R) (x : ↑X.fst) :
    (mkLinearMap (Submonoid.powers (φ f)) ↑X.fst) (r • x) =
      r • (mkLinearMap (Submonoid.powers (φ f)) ↑X.fst) x := sorry

/-- The global localization map viewed over the base ring. -/
noncomputable def globalLocalizationMap (φ : R →+* S) (f : R)
    (X : Pullback φ f) :
    ↑(global φ f X) →ₗ[R] ↑(localizedGlobalR φ f X) :=
  { toFun := fun x => (mkLinearMap (Submonoid.powers (φ f)) ↑X.fst) x
    map_add' := globalLocalizationMap_add φ f X
    map_smul' := globalLocalizationMap_smul φ f X }

/-- The Cech differential of a single-principal-open pullback datum. -/
@[stacks 0BP3 "single-principal-open Cech differential"]
noncomputable def differential (φ : R →+* S) (f : R) (X : Pullback φ f) :
  (↑(global φ f X) × ↑(localModuleCat φ f X)) →ₗ[R] ↑(localizedGlobalR φ f X) :=
  (globalLocalizationMap φ f X).coprod
    (-(localizedSideMap φ f X))

/-- The degree-zero module, as the kernel of `differential`. -/
@[stacks 0BP3 "single-principal-open H0 kernel"]
abbrev h0 (φ : R →+* S) (f : R) (X : Pullback φ f) :
    Submodule R (↑(global φ f X) × ↑(localModuleCat φ f X)) :=
  (differential φ f X).ker

/-- The principal-power torsion submodule of the degree-zero kernel. -/
@[stacks 0BP4 "single-principal-open H0 principal-power torsion"]
abbrev h0Torsion (φ : R →+* S) (f : R) (X : Pullback φ f) :
    Submodule R (h0 φ f X) :=
  (Submodule.torsion' R (h0 φ f X) (Submonoid.powers f) : Submodule R (h0 φ f X))

/-- The image of the global component in the localized global module. -/
@[stacks 0BP4 "single-principal-open localized base range"]
abbrev localizedBaseRange (φ : R →+* S) (f : R) (X : Pullback φ f) :
    Submodule S (Away (φ f) ↑X.fst) :=
  LinearMap.range (mkLinearMap (Submonoid.powers (φ f)) ↑X.fst)

/-- The localized global range is stable under the base-ring action. -/
theorem localizedBaseRange_smul_mem (φ : R →+* S) (f : R) (X : Pullback φ f)
    (r : R) {x : Away (φ f) ↑X.fst} (hx : x ∈ localizedBaseRange φ f X) :
    r • x ∈ localizedBaseRange φ f X := sorry

/-- The global image viewed as an `R`-submodule for the mod-torsion quotient. -/
@[stacks 0BP4 "single-principal-open localized base range over the base ring"]
abbrev localizedBaseRangeR (φ : R →+* S) (f : R) (X : Pullback φ f) :
    Submodule R (↑(localizedGlobalR φ f X)) :=
  { carrier := (localizedBaseRange φ f X).carrier
    zero_mem' := (localizedBaseRange φ f X).zero_mem
    add_mem' := fun hx hy => (localizedBaseRange φ f X).add_mem hx hy
    smul_mem' := fun r _ hx => localizedBaseRange_smul_mem φ f X r hx }

/-- The `f`-power torsion of `H⁰` lies in the kernel of its second projection. -/
theorem h0Torsion_le_ker_snd (φ : R →+* S) (f : R) (X : Pullback φ f) :
    h0Torsion φ f X ≤
      LinearMap.ker
        ((LinearMap.snd R (↑(global φ f X)) (↑(localModuleCat φ f X))).comp
          (h0 φ f X).subtype) := sorry

/-- The left map in the mod-torsion sequence, induced by the second projection of `H⁰`. -/
@[stacks 0BP4 "single-principal-open mod-torsion left map"]
noncomputable def h0TorsionLeftMap (φ : R →+* S) (f : R) (X : Pullback φ f) :
    (h0 φ f X) ⧸ h0Torsion φ f X →ₗ[R] ↑(localModuleCat φ f X) :=
  (h0Torsion φ f X).liftQ
    ((LinearMap.snd R (↑(global φ f X)) (↑(localModuleCat φ f X))).comp
      (h0 φ f X).subtype)
    (h0Torsion_le_ker_snd φ f X)

/-- The right map in the mod-torsion sequence, induced by the localized-side map. -/
@[stacks 0BP4 "single-principal-open mod-torsion right map"]
noncomputable abbrev h0TorsionRightMap (φ : R →+* S) (f : R) (X : Pullback φ f) :
    ↑(localModuleCat φ f X) →ₗ[R]
      (↑(localizedGlobalR φ f X)) ⧸ localizedBaseRangeR φ f X :=
  (localizedBaseRangeR φ f X).mkQ.comp (localizedSideMap φ f X)

/-- The quotient maps in the mod-torsion sequence form a complex. -/
@[stacks 0BP4 "single-principal-open mod-torsion complex"]
theorem h0Torsion_comp_eq_zero (φ : R →+* S) (f : R) (X : Pullback φ f) :
    (h0TorsionRightMap φ f X).comp (h0TorsionLeftMap φ f X) = 0 := sorry

/-- The canonical mod-torsion short complex. -/
@[stacks 0BP4 "single-principal-open mod-torsion sequence"]
noncomputable def h0TorsionSequence (φ : R →+* S) (f : R) (X : Pullback φ f) :
    ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero
    (h0TorsionLeftMap φ f X)
    (h0TorsionRightMap φ f X)
    (h0Torsion_comp_eq_zero φ f X)

namespace BaseChange

variable [Algebra R S]

/-- The algebra-specialized pullback for base-changing the mod-torsion sequence. -/
abbrev Pullback (f : R) :=
  @LocalizedModule.Away.FormalGluing.Single.Pullback R S _ _
    (algebraMap R S) f

/-- The localized first component carries the canonical `R`--`S` scalar tower. -/
@[stacks 0BP5 "scalar tower on the base-changed localized component"]
instance localizedGlobalTower (f : R)
    (X : @LocalizedModule.Away.FormalGluing.Single.Pullback R S _ _
      (algebraMap R S) f) :
    IsScalarTower R S (LocalizedModule.Away (algebraMap R S f) ↑X.fst) := sorry

/-- The quotient `H⁰/H⁰[f^∞]` maps canonically to the localized first component. -/
@[stacks 0BP5 "base-changed mod-torsion comparison map"]
noncomputable abbrev quotientToLocalizedGlobal (f : R)
    (X : Pullback (R := R) (S := S) f) :
    (h0 (algebraMap R S) f X) ⧸ h0Torsion (algebraMap R S) f X →ₗ[R]
      Away (algebraMap R S f) ↑X.fst :=
  (localizedSideMap (algebraMap R S) f X).comp
    (h0TorsionLeftMap (algebraMap R S) f X)

/-- The left map
`S ⊗[R] (H⁰/H⁰[f^∞]) → (X.fst)_f` in the base-changed sequence. -/
@[stacks 0BP5 "base-changed mod-torsion left map"]
noncomputable abbrev leftMap (f : R) (X : Pullback (R := R) (S := S) f) :
    S ⊗[R] ((h0 (algebraMap R S) f X) ⧸ h0Torsion (algebraMap R S) f X) →ₗ[S]
      Away (algebraMap R S f) ↑X.fst :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : S →ₗ[S] S).smulRight
      (quotientToLocalizedGlobal f X))

/-- The quotient map `(X.fst)_f → (X.fst)_f/X.fst`. -/
@[stacks 0BP5 "base-changed mod-torsion right map"]
noncomputable abbrev rightMap (f : R) (X : Pullback (R := R) (S := S) f) :
    Away (algebraMap R S f) ↑X.fst →ₗ[S]
      (Away (algebraMap R S f) ↑X.fst) ⧸
        localizedBaseRange (R := R) (S := S) (algebraMap R S) f X :=
  (localizedBaseRange (R := R) (S := S) (algebraMap R S) f X).mkQ

/-- The two base-changed quotient maps form a complex. -/
@[stacks 0BP5 "base-changed mod-torsion complex"]
theorem comp_eq_zero (f : R) (X : Pullback (R := R) (S := S) f) :
    (rightMap f X).comp (leftMap f X) = 0 := sorry

/-- The canonical base-changed mod-torsion short complex. -/
@[stacks 0BP5 "base-changed mod-torsion sequence"]
noncomputable def sequence (f : R) (X : Pullback (R := R) (S := S) f) :
    ShortComplex (ModuleCat S) :=
  ModuleCat.shortComplexOfCompEqZero
    (leftMap f X) (rightMap f X) (comp_eq_zero f X)

end BaseChange

/-- The canonical kernel short complex for the single-principal-open
differential. -/
@[stacks 0BP3 "single-principal-open H0 kernel sequence"]
noncomputable abbrev h0Sequence (φ : R →+* S) (f : R) (X : Pullback φ f) :
    ShortComplex (ModuleCat R) :=
  (differential φ f X).shortComplexKer

/-- Surjectivity of the Cech differential makes the canonical kernel sequence
short exact. -/
@[stacks 0BP3 "single-principal-open H⁰ short exact sequence"]
theorem h0Sequence_shortExact_of_surjective
    (φ : R →+* S) (f : R)
    (X : CategoricalPullback
      (ModuleCat.extendScalars (algebraMap S (Localization.Away (φ f))))
      (ModuleCat.extendScalars (overlapMap φ f)))
    (hsurj : Function.Surjective (differential φ f X)) :
    (h0Sequence φ f X).ShortExact := sorry

end LocalizedModule.Away.FormalGluing.Single
