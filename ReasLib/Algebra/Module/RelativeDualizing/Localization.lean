/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import ReasLib.Algebra.Module.RelativeDualizing
public import ReasLib.Algebra.Module.LocalizedModule.Away.BaseChange
public import ReasLib.Algebra.Module.LocalizedModule.Equiv
public import ReasLib.LinearAlgebra.TensorProduct.Bimodule.Associator
public import ReasLib.RingTheory.Localization.Away.Relative
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Algebra.DualModule TensorProduct TensorProduct.Right

universe u v

namespace Algebra.RelativeDualizingModule

variable (A : Type u) (B' B : Type v)
variable [CommRing A] [CommRing B'] [CommRing B]
variable [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]

/-- The canonical map from the localization of the finite model `B'` to a target `B` in which
`f : A` is invertible. -/
noncomputable def awayFactorMap (f : A) [Algebra (Localization.Away f) B]
    [IsScalarTower A (Localization.Away f) B] :
    Localization.Away (algebraMap A B' f) →+* B :=
  IsLocalization.Away.lift (algebraMap A B' f)
    (Eq.mp
      (congrArg IsUnit
        ((IsScalarTower.algebraMap_apply A (Localization.Away f) B f).symm.trans
          (IsScalarTower.algebraMap_apply A B' B f)))
      ((IsLocalization.Away.algebraMap_isUnit f).map
        (algebraMap (Localization.Away f) B)))

/-- The map `awayFactorMap` extends the original map from the chosen finite model to `B`. -/
theorem awayFactorMap_comp (f : A) [Algebra (Localization.Away f) B]
    [IsScalarTower A (Localization.Away f) B] :
    (awayFactorMap A B' B f).comp
        (algebraMap B' (Localization.Away (algebraMap A B' f))) =
      algebraMap B' B := sorry

/-- The relative action on `B` induced by `awayFactorMap` is compatible with the localized
base-ring action. -/
theorem awayFactorMap_isScalarTower (f : A) [Algebra (Localization.Away f) B]
    [IsScalarTower A (Localization.Away f) B] :
    -- Local instance justification (instance diamond): this action is induced by the chosen
    -- factorization through `Localization.Away f` and can compete with another action on `B`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away (algebraMap A B' f)) B :=
      (awayFactorMap A B' B f).toAlgebra
    -- Local instance justification (instance diamond): this is the action on the localized
    -- finite model induced by the fixed map `A → B'`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) :=
      Localization.Away.Relative.mapAlgebra (algebraMap A B') f
    IsScalarTower (Localization.Away f)
      (Localization.Away (algebraMap A B' f)) B := sorry

/-- Localizing the base of a finite-type quasi-finite map along a factorization preserves
finite-type quasi-finiteness. -/
theorem quasiFiniteAwayBase [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) (f : A)
    [Algebra (Localization.Away f) B] [IsScalarTower A (Localization.Away f) B] :
    Algebra.FiniteType.QuasiFinite (Localization.Away f) B := sorry

/-- Localizing the target of a finite-type quasi-finite map preserves finite-type
quasi-finiteness. -/
theorem quasiFiniteAwayTarget [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) (g : B) :
    Algebra.FiniteType.QuasiFinite A (Localization.Away g) := sorry

/-- The finite chosen model remains finite after simultaneously localizing its base. -/
theorem finiteAwayBase [IsNoetherianRing A] [Module.Finite A B'] (f : A) :
    -- Local instance justification (instance diamond): this is the action induced by
    -- `Localization.awayMap (algebraMap A B') f`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) :=
      Localization.Away.Relative.mapAlgebra (algebraMap A B') f
    Module.Finite (Localization.Away f)
      (Localization.Away (algebraMap A B' f)) := sorry

/-- The localized finite model still presents `Spec B` as an open subscheme when the original
chosen model does and the map `A → B` factors through `Localization.Away f`. -/
theorem openAwayBase
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (f : A) [Algebra (Localization.Away f) B]
    [IsScalarTower A (Localization.Away f) B] :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (awayFactorMap A B' B f))) := sorry

/-- Localizing the target preserves the chosen open-immersion presentation. -/
theorem openAwayTarget
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (g : B) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (algebraMap B' (Localization.Away g)))) := sorry

/-- Localization of the `A`-linear dual of the finite model is canonically its dual after
localizing both `A` and `B'`. -/
noncomputable def awayDualEquiv [IsNoetherianRing A] [Module.Finite A B'] (f : A) :
    -- Local instance justification (instance diamond): this is the action induced by the
    -- fixed map `A → B'`, not a globally preferred action on the target localization.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) :=
      Localization.Away.Relative.mapAlgebra (algebraMap A B') f
    LocalizedModule.Away f (Module.Dual A B') ≃ₗ[Localization.Away f]
      Module.Dual (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) :=
  -- Local instance justification (proof-local temporary data): finite presentation is
  -- canonically derived here from Noetherianity and finiteness for the Hom-localization theorem.
  -- Local instance justification (proof-local temporary data): this transported finiteness data is needed only for the localized comparison.
  letI : Module.FinitePresentation A B' := Module.finitePresentation_of_finite A B'
  -- Local instance justification (instance diamond): this pins the action induced by the
  -- selected map `A → B'` only for the localization comparison.
  -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
  letI : Algebra (Localization.Away f)
      (Localization.Away (algebraMap A B' f)) :=
    Localization.Away.Relative.mapAlgebra (algebraMap A B') f
  -- Local instance justification (instance diamond): the tower belongs to that selected
  -- relative localization action.
  -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
  letI : IsScalarTower A (Localization.Away f)
      (Localization.Away (algebraMap A B' f)) :=
    Localization.Away.Relative.algebraMapAlgebra_isScalarTower f
  let sourceEquiv := LinearEquiv.extendScalarsOfIsLocalization
    (Submonoid.powers f) (Localization.Away f)
      (Module.FinitePresentation.linearEquivMapExtendScalars (Submonoid.powers f))
  let modelEquiv := LinearEquiv.extendScalarsOfIsLocalization
    (Submonoid.powers f) (Localization.Away f)
      (IsLocalizedModule.iso (Submonoid.powers f)
        (IsScalarTower.toAlgHom A B'
          (Localization.Away (algebraMap A B' f))).toLinearMap)
  sourceEquiv.trans
    (LinearEquiv.arrowCongr modelEquiv
      (LocalizedModule.selfEquiv (Submonoid.powers f)))

/-- On canonical localized functionals, `awayDualEquiv` is the Hom-localization comparison
followed by the canonical identifications of the localized source and target modules. -/
theorem awayDualEquiv_apply [IsNoetherianRing A] [Module.Finite A B'] (f : A)
    (φ : Module.Dual A B') (b : B') :
    -- Local instance justification (instance diamond): this is the action induced by the
    -- fixed map `A → B'`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) :=
      Localization.Away.Relative.mapAlgebra (algebraMap A B') f
    awayDualEquiv A B' f (LocalizedModule.mk φ 1)
        (algebraMap B' (Localization.Away (algebraMap A B' f)) b) =
      algebraMap A (Localization.Away f) (φ b) := sorry

/-- The scalar action on the chosen relative dualizing module inherited from a factorization
through `Localization.Away f` is compatible with its original `A`-module structure. -/
private theorem awayLocalizedDualToTensor_isScalarTower (f : A)
    [Algebra (Localization.Away f) B] [IsScalarTower A (Localization.Away f) B] :
    IsScalarTower A (Localization.Away f) (Module.Dual A B' ⊗[B'] B) := sorry

/-- Once `f` is invertible in `B`, the localized dual maps canonically into the original
chosen relative dualizing module by absorbing denominators into its `B`-factor. -/
private noncomputable def awayLocalizedDualToTensor (f : A)
    [Algebra (Localization.Away f) B] [IsScalarTower A (Localization.Away f) B] :
    LocalizedModule.Away f (Module.Dual A B') →ₗ[Localization.Away f]
      Module.Dual A B' ⊗[B'] B :=
  -- Local instance justification (proof-local temporary data): this records compatibility of
  -- the inherited localized-base action with the original `A`-action at this construction.
  -- Local instance justification (proof-local temporary data): this transported scalar-tower data is needed only for the localized comparison.
  letI : IsScalarTower A (Localization.Away f) (Module.Dual A B' ⊗[B'] B) :=
    awayLocalizedDualToTensor_isScalarTower A B' B f
  let numerator : Module.Dual A B' →ₗ[A] (Module.Dual A B' ⊗[B'] B) :=
    { toFun := fun φ ↦ φ ⊗ₜ[B'] 1
      map_add' := sorry
      map_smul' := sorry }
  LinearMap.extendScalarsOfIsLocalization (Submonoid.powers f)
    (Localization.Away f)
      (LocalizedModule.lift (Submonoid.powers f) numerator (fun s ↦
        Eq.mp
          (congrArg IsUnit
            ((Algebra.lsmul A (A := Localization.Away f) A
              (Module.Dual A B' ⊗[B'] B)).commutes s))
          ((IsLocalization.map_units (Localization.Away f) s).map
            (Algebra.lsmul A (A := Localization.Away f) A
              (Module.Dual A B' ⊗[B'] B)))))

/-- The denominator-absorption map sends a functional with denominator `1` to its pure tensor
with `1 : B`. -/
private theorem awayLocalizedDualToTensor_mk (f : A)
    [Algebra (Localization.Away f) B] [IsScalarTower A (Localization.Away f) B]
    (φ : Module.Dual A B') :
    awayLocalizedDualToTensor A B' B f (LocalizedModule.mk φ 1) =
      φ ⊗ₜ[B'] (1 : B) := sorry

/-- The forward comparison for base localization sends a pure tensor to the localized
functional tensored with the same target coefficient. -/
private noncomputable def awayBaseHom [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (f : A) [Algebra (Localization.Away f) B]
    [IsScalarTower A (Localization.Away f) B] :
    -- Local instance justification (instance diamond): this target action is induced by the
    -- source factorization through `Localization.Away f`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away (algebraMap A B' f)) B :=
      (awayFactorMap A B' B f).toAlgebra
    -- Local instance justification (instance diamond): this pins the relative action induced
    -- by the selected map `A → B'`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) :=
      Localization.Away.Relative.mapAlgebra (algebraMap A B') f
    -- Local instance justification (instance diamond): the tower uses the two selected
    -- factorization actions above.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : IsScalarTower (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) B :=
      awayFactorMap_isScalarTower A B' B f
    -- Local instance justification (proof-local temporary data): finiteness is transported
    -- from the chosen finite model only for this localized presentation.
    -- Local instance justification (proof-local temporary data): this transported finiteness data is needed only for the localized comparison.
    letI : Module.Finite (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) := finiteAwayBase A B' f
    RelativeDualizingModule.of A B' B h_quasiFinite h_open →ₗ[B]
      RelativeDualizingModule.of (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) B
          (quasiFiniteAwayBase A B h_quasiFinite f)
          (openAwayBase A B' B h_open f) :=
  -- Local instance justification (instance diamond): this target action is induced by the
  -- source factorization through `Localization.Away f`.
  -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
  letI : Algebra (Localization.Away (algebraMap A B' f)) B :=
    (awayFactorMap A B' B f).toAlgebra
  -- Local instance justification (instance diamond): this pins the relative action induced
  -- by the selected map `A → B'`.
  -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
  letI : Algebra (Localization.Away f)
      (Localization.Away (algebraMap A B' f)) :=
    Localization.Away.Relative.mapAlgebra (algebraMap A B') f
  -- Local instance justification (instance diamond): the tower uses the two selected
  -- factorization actions above.
  -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
  letI : IsScalarTower (Localization.Away f)
      (Localization.Away (algebraMap A B' f)) B :=
    awayFactorMap_isScalarTower A B' B f
  -- Local instance justification (proof-local temporary data): finiteness is transported
  -- from the chosen finite model only for this localized presentation.
  -- Local instance justification (proof-local temporary data): this transported finiteness data is needed only for the localized comparison.
  letI : Module.Finite (Localization.Away f)
      (Localization.Away (algebraMap A B' f)) := finiteAwayBase A B' f
  { toFun := TensorProduct.liftAddHom
      ({ toFun := fun φ ↦
          { toFun := fun b ↦
              awayDualEquiv A B' f (LocalizedModule.mk φ 1) ⊗ₜ[
                Localization.Away (algebraMap A B' f)] b
            map_zero' := sorry
            map_add' := sorry }
         map_zero' := sorry
         map_add' := sorry } :
        Module.Dual A B' →+
          (B →+ (Module.Dual (Localization.Away f)
            (Localization.Away (algebraMap A B' f)) ⊗[
              Localization.Away (algebraMap A B' f)] B)))
      (fun _ _ _ ↦ sorry)
    map_add' := sorry
    map_smul' := sorry }

/-- The inverse base-localization comparison absorbs the localized functional's denominator
into the target `B`-factor. -/
private noncomputable def awayBaseInv [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (f : A) [Algebra (Localization.Away f) B]
    [IsScalarTower A (Localization.Away f) B] :
    -- Local instance justification (instance diamond): this target action is induced by the
    -- source factorization through `Localization.Away f`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away (algebraMap A B' f)) B :=
      (awayFactorMap A B' B f).toAlgebra
    -- Local instance justification (instance diamond): this pins the relative action induced
    -- by the selected map `A → B'`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) :=
      Localization.Away.Relative.mapAlgebra (algebraMap A B') f
    -- Local instance justification (instance diamond): the tower uses the two selected
    -- factorization actions above.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : IsScalarTower (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) B :=
      awayFactorMap_isScalarTower A B' B f
    -- Local instance justification (proof-local temporary data): finiteness is transported
    -- from the chosen finite model only for this localized presentation.
    -- Local instance justification (proof-local temporary data): this transported finiteness data is needed only for the localized comparison.
    letI : Module.Finite (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) := finiteAwayBase A B' f
    RelativeDualizingModule.of (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) B
          (quasiFiniteAwayBase A B h_quasiFinite f)
          (openAwayBase A B' B h_open f) →ₗ[B]
      RelativeDualizingModule.of A B' B h_quasiFinite h_open :=
  -- Local instance justification (instance diamond): this target action is induced by the
  -- source factorization through `Localization.Away f`.
  -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
  letI : Algebra (Localization.Away (algebraMap A B' f)) B :=
    (awayFactorMap A B' B f).toAlgebra
  -- Local instance justification (instance diamond): this pins the relative action induced
  -- by the selected map `A → B'`.
  -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
  letI : Algebra (Localization.Away f)
      (Localization.Away (algebraMap A B' f)) :=
    Localization.Away.Relative.mapAlgebra (algebraMap A B') f
  -- Local instance justification (instance diamond): the tower uses the two selected
  -- factorization actions above.
  -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
  letI : IsScalarTower (Localization.Away f)
      (Localization.Away (algebraMap A B' f)) B :=
    awayFactorMap_isScalarTower A B' B f
  -- Local instance justification (proof-local temporary data): finiteness is transported
  -- from the chosen finite model only for this localized presentation.
  -- Local instance justification (proof-local temporary data): this transported finiteness data is needed only for the localized comparison.
  letI : Module.Finite (Localization.Away f)
      (Localization.Away (algebraMap A B' f)) := finiteAwayBase A B' f
  { toFun := TensorProduct.liftAddHom
      ({ toFun := fun ψ ↦
          { toFun := fun b ↦ b • awayLocalizedDualToTensor A B' B f
                ((awayDualEquiv A B' f).symm ψ)
            map_zero' := sorry
            map_add' := sorry }
         map_zero' := sorry
         map_add' := sorry } :
        Module.Dual (Localization.Away f)
            (Localization.Away (algebraMap A B' f)) →+
          (B →+ (Module.Dual A B' ⊗[B'] B)))
      (fun _ _ _ ↦ sorry)
    map_add' := sorry
    map_smul' := sorry }

/-- Base localization canonically identifies the chosen relative dualizing `B`-modules for
`A → B' → B` and `A_f → B'_f → B`. -/
@[no_expose]
noncomputable def awayBaseIso [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (f : A) [Algebra (Localization.Away f) B]
    [IsScalarTower A (Localization.Away f) B] :
    -- Local instance justification (instance diamond): this target action is induced by the
    -- source factorization through `Localization.Away f`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away (algebraMap A B' f)) B :=
      (awayFactorMap A B' B f).toAlgebra
    -- Local instance justification (instance diamond): this pins the relative action induced
    -- by the selected map `A → B'`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) :=
      Localization.Away.Relative.mapAlgebra (algebraMap A B') f
    -- Local instance justification (instance diamond): the tower uses the two selected
    -- factorization actions above.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : IsScalarTower (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) B :=
      awayFactorMap_isScalarTower A B' B f
    -- Local instance justification (proof-local temporary data): finiteness is transported
    -- from the chosen finite model only for this localized presentation.
    -- Local instance justification (proof-local temporary data): this transported finiteness data is needed only for the localized comparison.
    letI : Module.Finite (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) := finiteAwayBase A B' f
    RelativeDualizingModule.of A B' B h_quasiFinite h_open ≅
      RelativeDualizingModule.of (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) B
          (quasiFiniteAwayBase A B h_quasiFinite f)
          (openAwayBase A B' B h_open f) :=
  -- Local instance justification (instance diamond): this target action is induced by the
  -- source factorization through `Localization.Away f`.
  -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
  letI : Algebra (Localization.Away (algebraMap A B' f)) B :=
    (awayFactorMap A B' B f).toAlgebra
  -- Local instance justification (instance diamond): this pins the relative action induced
  -- by the selected map `A → B'`.
  -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
  letI : Algebra (Localization.Away f)
      (Localization.Away (algebraMap A B' f)) :=
    Localization.Away.Relative.mapAlgebra (algebraMap A B') f
  -- Local instance justification (instance diamond): the tower uses the two selected
  -- factorization actions above.
  -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
  letI : IsScalarTower (Localization.Away f)
      (Localization.Away (algebraMap A B' f)) B :=
    awayFactorMap_isScalarTower A B' B f
  -- Local instance justification (proof-local temporary data): finiteness is transported
  -- from the chosen finite model only for this localized presentation.
  -- Local instance justification (proof-local temporary data): this transported finiteness data is needed only for the localized comparison.
  letI : Module.Finite (Localization.Away f)
      (Localization.Away (algebraMap A B' f)) := finiteAwayBase A B' f
  { hom := ModuleCat.ofHom (awayBaseHom A B' B h_quasiFinite h_open f)
    inv := ModuleCat.ofHom (awayBaseInv A B' B h_quasiFinite h_open f)
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The forward base-localization isomorphism acts on pure tensors by localizing the functional
and retaining its `B`-coefficient. -/
theorem awayBaseIso_hom_tmul [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (f : A) [Algebra (Localization.Away f) B]
    [IsScalarTower A (Localization.Away f) B]
    (φ : Module.Dual A B') (b : B) :
    -- Local instance justification (instance diamond): this target action is induced by the
    -- source factorization through `Localization.Away f`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away (algebraMap A B' f)) B :=
      (awayFactorMap A B' B f).toAlgebra
    -- Local instance justification (instance diamond): this pins the relative action induced
    -- by the selected map `A → B'`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) :=
      Localization.Away.Relative.mapAlgebra (algebraMap A B') f
    -- Local instance justification (instance diamond): the tower uses the two selected
    -- factorization actions above.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : IsScalarTower (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) B :=
      awayFactorMap_isScalarTower A B' B f
    -- Local instance justification (proof-local temporary data): finiteness is transported
    -- from the chosen finite model only for this localized presentation.
    -- Local instance justification (proof-local temporary data): this transported finiteness data is needed only for the localized comparison.
    letI : Module.Finite (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) := finiteAwayBase A B' f
    (awayBaseIso A B' B h_quasiFinite h_open f).hom (φ ⊗ₜ[B'] b) =
      awayDualEquiv A B' f (LocalizedModule.mk φ 1) ⊗ₜ[
        Localization.Away (algebraMap A B' f)] b := sorry

/-- The forward target-localization comparison sends a localized tensor to the tensor obtained
by localizing its `B`-coefficient. -/
private noncomputable def awayTargetHom [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (g : B) :
    LocalizedModule.Away g
        (RelativeDualizingModule.of A B' B h_quasiFinite h_open) →ₗ[
          Localization.Away g]
      RelativeDualizingModule.of A B' (Localization.Away g)
        (quasiFiniteAwayTarget A B h_quasiFinite g)
        (openAwayTarget B' B h_open g) :=
  let numerator :
      RelativeDualizingModule.of A B' B h_quasiFinite h_open →ₗ[B]
        RelativeDualizingModule.of A B' (Localization.Away g)
          (quasiFiniteAwayTarget A B h_quasiFinite g)
          (openAwayTarget B' B h_open g) :=
    { toFun := TensorProduct.liftAddHom
        ({ toFun := fun φ ↦
            { toFun := fun b ↦
                φ ⊗ₜ[B'] algebraMap B (Localization.Away g) b
              map_zero' := sorry
              map_add' := sorry }
           map_zero' := sorry
           map_add' := sorry } :
          Module.Dual A B' →+
            (B →+ RelativeDualizingModule.of A B' (Localization.Away g)
              (quasiFiniteAwayTarget A B h_quasiFinite g)
              (openAwayTarget B' B h_open g)))
        (fun _ _ _ ↦ sorry)
      map_add' := sorry
      map_smul' := sorry }
  LinearMap.extendScalarsOfIsLocalization (Submonoid.powers g)
    (Localization.Away g)
      (LocalizedModule.lift (Submonoid.powers g) numerator (fun s ↦
        Eq.mp
          (congrArg IsUnit
            ((Algebra.lsmul B (A := Localization.Away g) B
                (RelativeDualizingModule.of A B' (Localization.Away g)
                  (quasiFiniteAwayTarget A B h_quasiFinite g)
                  (openAwayTarget B' B h_open g))).commutes s))
          ((IsLocalization.map_units (Localization.Away g) s).map
            (Algebra.lsmul B (A := Localization.Away g) B
                (RelativeDualizingModule.of A B' (Localization.Away g)
                  (quasiFiniteAwayTarget A B h_quasiFinite g)
                  (openAwayTarget B' B h_open g))))))

/-- The inverse target-localization comparison tensors a functional with a localized
coefficient and regards the result as a localized tensor. -/
private noncomputable def awayTargetInv [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (g : B) :
    RelativeDualizingModule.of A B' (Localization.Away g)
        (quasiFiniteAwayTarget A B h_quasiFinite g)
        (openAwayTarget B' B h_open g) →ₗ[Localization.Away g]
      LocalizedModule.Away g
        (RelativeDualizingModule.of A B' B h_quasiFinite h_open) :=
  { toFun := TensorProduct.liftAddHom
      ({ toFun := fun φ ↦
          { toFun := fun b ↦ b •
                LocalizedModule.mk (φ ⊗ₜ[B'] (1 : B)) 1
            map_zero' := sorry
            map_add' := sorry }
         map_zero' := sorry
         map_add' := sorry } :
        Module.Dual A B' →+
          (Localization.Away g →+
            LocalizedModule.Away g
              (RelativeDualizingModule.of A B' B h_quasiFinite h_open)))
      (fun _ _ _ ↦ sorry)
    map_add' := sorry
    map_smul' := sorry }

/-- Localizing the chosen relative dualizing module at `g : B` canonically gives the
chosen relative dualizing module of `A → Localization.Away g`. -/
@[no_expose]
noncomputable def awayTargetIso [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (g : B) :
    ModuleCat.of (Localization.Away g)
        (LocalizedModule.Away g
          (RelativeDualizingModule.of A B' B h_quasiFinite h_open)) ≅
      RelativeDualizingModule.of A B' (Localization.Away g)
        (quasiFiniteAwayTarget A B h_quasiFinite g)
        (openAwayTarget B' B h_open g) :=
  { hom := ModuleCat.ofHom
      (awayTargetHom A B' B h_quasiFinite h_open g)
    inv := ModuleCat.ofHom
      (awayTargetInv A B' B h_quasiFinite h_open g)
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The target-localization isomorphism sends a localized pure tensor to the same functional
tensored with the localized coefficient. -/
theorem awayTargetIso_hom_mk [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (g : B) (φ : Module.Dual A B') (b : B) :
    (awayTargetIso A B' B h_quasiFinite h_open g).hom
        (LocalizedModule.mk (φ ⊗ₜ[B'] b) 1) =
      φ ⊗ₜ[B'] algebraMap B (Localization.Away g) b := sorry

/-- Simultaneous localization of the source and target canonically identifies the localized
relative dualizing module with the relative dualizing module of the localized map. -/
noncomputable def awayIso [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (f : A) :
    -- Local instance justification (instance diamond): this is the relative localization
    -- action induced by the fixed map `A → B`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away f)
        (Localization.Away (algebraMap A B f)) :=
      Localization.Away.Relative.mapAlgebra (algebraMap A B) f
    -- Local instance justification (instance diamond): the tower belongs to the selected
    -- relative localization action on `Localization.Away (algebraMap A B f)`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : IsScalarTower A (Localization.Away f)
        (Localization.Away (algebraMap A B f)) :=
      Localization.Away.Relative.algebraMapAlgebra_isScalarTower f
    let h_quasiFiniteTarget :=
      quasiFiniteAwayTarget A B h_quasiFinite (algebraMap A B f)
    let h_openTarget :=
      openAwayTarget B' B h_open (algebraMap A B f)
    -- Local instance justification (instance diamond): this target action is induced by the
    -- localized chosen-model factorization.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away (algebraMap A B' f))
        (Localization.Away (algebraMap A B f)) :=
      (awayFactorMap A B' (Localization.Away (algebraMap A B f)) f).toAlgebra
    -- Local instance justification (instance diamond): this is the action induced by the
    -- fixed chosen-model map `A → B'`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) :=
      Localization.Away.Relative.mapAlgebra (algebraMap A B') f
    -- Local instance justification (instance diamond): the tower uses the two selected
    -- localization actions above.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : IsScalarTower (Localization.Away f)
        (Localization.Away (algebraMap A B' f))
        (Localization.Away (algebraMap A B f)) :=
      awayFactorMap_isScalarTower A B'
        (Localization.Away (algebraMap A B f)) f
    -- Local instance justification (proof-local temporary data): finiteness is transported
    -- from the chosen finite model for this localized presentation.
    -- Local instance justification (proof-local temporary data): this transported finiteness data is needed only for the localized comparison.
    letI : Module.Finite (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) := finiteAwayBase A B' f
    RelativeDualizingModule.of (Localization.Away f)
        (Localization.Away (algebraMap A B' f))
        (Localization.Away (algebraMap A B f))
          (quasiFiniteAwayBase A
            (Localization.Away (algebraMap A B f)) h_quasiFiniteTarget f)
          (openAwayBase A B' (Localization.Away (algebraMap A B f))
            h_openTarget f) ≅
      ModuleCat.of (Localization.Away (algebraMap A B f))
        (LocalizedModule.Away (algebraMap A B f)
          (RelativeDualizingModule.of A B' B h_quasiFinite h_open)) :=
  -- Local instance justification (instance diamond): this is the relative localization
  -- action induced by the fixed map `A → B`.
  -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
  letI : Algebra (Localization.Away f)
      (Localization.Away (algebraMap A B f)) :=
    Localization.Away.Relative.mapAlgebra (algebraMap A B) f
  -- Local instance justification (instance diamond): the tower belongs to the selected
  -- relative localization action on `Localization.Away (algebraMap A B f)`.
  -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
  letI : IsScalarTower A (Localization.Away f)
      (Localization.Away (algebraMap A B f)) :=
    Localization.Away.Relative.algebraMapAlgebra_isScalarTower f
  let h_quasiFiniteTarget :=
    quasiFiniteAwayTarget A B h_quasiFinite (algebraMap A B f)
  let h_openTarget :=
    openAwayTarget B' B h_open (algebraMap A B f)
  (awayBaseIso A B' (Localization.Away (algebraMap A B f))
      h_quasiFiniteTarget h_openTarget f).symm ≪≫
    (awayTargetIso A B' B h_quasiFinite h_open
      (algebraMap A B f)).symm

/-- The simultaneous localization comparison is the source-localization comparison followed
by the inverse target-localization comparison. -/
theorem awayIso_eq [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (f : A) :
    -- Local instance justification (instance diamond): this is the relative localization
    -- action induced by the fixed map `A → B`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away f)
        (Localization.Away (algebraMap A B f)) :=
      Localization.Away.Relative.mapAlgebra (algebraMap A B) f
    -- Local instance justification (instance diamond): the tower belongs to the selected
    -- relative localization action on `Localization.Away (algebraMap A B f)`.
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : IsScalarTower A (Localization.Away f)
        (Localization.Away (algebraMap A B f)) :=
      Localization.Away.Relative.algebraMapAlgebra_isScalarTower f
    let h_quasiFiniteTarget :=
      quasiFiniteAwayTarget A B h_quasiFinite (algebraMap A B f)
    let h_openTarget :=
      openAwayTarget B' B h_open (algebraMap A B f)
    awayIso A B' B h_quasiFinite h_open f =
      (awayBaseIso A B' (Localization.Away (algebraMap A B f))
        h_quasiFiniteTarget h_openTarget f).symm ≪≫
        (awayTargetIso A B' B h_quasiFinite h_open
          (algebraMap A B f)).symm := sorry

end Algebra.RelativeDualizingModule
