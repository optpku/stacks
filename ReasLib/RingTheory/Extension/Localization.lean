/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Map

/-!
# Localization of Algebra Extensions

This file owns the canonical morphism from an algebra extension to a
localization of its target.  It also exposes the induced cotangent map as named
data and proves that this map is a localization of modules.

Localization of a universal first-order thickening is a separate property leaf
in `ReasLib.RingTheory.Extension.FirstOrder.Localization`.

@stack 04EE
-/

@[expose] public section

noncomputable section

open Algebra
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v w x

namespace Algebra.Extension.TargetLocalization

variable {R : Type u} {S : Type v} {S' : Type x}
variable [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
variable (P : Extension.{w} R S) (T : Submonoid S)
variable [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
variable [IsLocalization T S']

/-- The canonical morphism from an extension to the extension obtained by
localizing its target. -/
@[stacks 04EE "extension morphism to a target localization"]
noncomputable def hom :
    P.Hom (P.localization T : Extension R S') where
  toRingHom :=
    algebraMap P.Ring (Localization (T.comap (algebraMap P.Ring S)))
  toRingHom_algebraMap _ := rfl
  algebraMap_toRingHom x :=
    congrArg (fun f : P.Ring →+* S' ↦ f x) (IsLocalization.map_comp le_rfl)

/-- The kernel of a localized extension is the image of the original kernel
in the localized extension ring. -/
@[stacks 04EE "kernel of a target-localized extension"]
theorem ker_eq_map :
    (P.localization T : Extension R S').ker =
      P.ker.map (hom P T).toRingHom := by
  change RingHom.ker
      (IsLocalization.map
        (S := Localization (T.comap (algebraMap P.Ring S)))
        (M := T.comap (algebraMap P.Ring S)) (T := T)
        S' (algebraMap P.Ring S) le_rfl) = _
  exact IsLocalization.ker_map
    (R := P.Ring)
    (S := Localization (T.comap (algebraMap P.Ring S)))
    (P := S)
    (Q := S')
    (g := algebraMap P.Ring S)
    (Submonoid.map_comap_eq_of_surjective P.algebraMap_surjective T)

/-- The canonical map from the cotangent module of an extension to the
cotangent module after target localization. -/
@[stacks 04EE "cotangent map to a target localization"]
noncomputable def cotangentMap :
    P.Cotangent →ₗ[S] (P.localization T : Extension R S').Cotangent :=
  Extension.Cotangent.map (hom P T)

/-- The canonical cotangent map to a target localization realizes localization
of the original cotangent module. -/
@[stacks 04EE "localized conormal module"]
theorem cotangentMap_isLocalizedModule :
    IsLocalizedModule T (cotangentMap (S' := S') P T) := by
  -- Proof-local instance justification (explicit-map choice): the `P.Ring`-action on `S'` is the
  -- composite through `S`; the carrier `S'` alone does not determine this algebra structure.
  letI : Algebra P.Ring S' :=
    Algebra.compHom S' (algebraMap P.Ring S)
  letI : IsScalarTower P.Ring S S' :=
    IsScalarTower.of_algebraMap_eq' rfl
  let U : Submonoid P.Ring := T.comap (algebraMap P.Ring S)
  let A' := Localization U
  let locMap : A' →+* S' :=
    IsLocalization.map (S := A') (M := U) (T := T)
      S' (algebraMap P.Ring S) le_rfl
  -- This algebra structure is pinned to the explicit localization comparison `locMap`.
  letI : Algebra A' S' := locMap.toAlgebra
  letI : IsScalarTower P.Ring A' S' :=
    IsScalarTower.of_algebraMap_eq' <| by
      rw [RingHom.algebraMap_toAlgebra]
      exact (IsLocalization.map_comp (Q := S')
        (g := algebraMap P.Ring S) le_rfl).symm
  let K : Ideal A' := RingHom.ker locMap
  have hT : Submonoid.map (algebraMap P.Ring S) U = T :=
    Submonoid.map_comap_eq_of_surjective P.algebraMap_surjective T
  let kmap : P.ker →ₗ[P.Ring] K :=
    RingHom.toKerIsLocalization A' S' (algebraMap P.Ring S) le_rfl
  -- The remaining local instances are proposition-valued localization witnesses consumed by
  -- Mathlib's `IsLocalizedModule` API; they introduce no new carrier, map, or algebra choice.
  letI : IsLocalizedModule U kmap :=
    RingHom.toKerIsLocalization_isLocalizedModule S' (algebraMap P.Ring S) hT

  -- Localize the presentation `P.ker / P.ker²` and identify its target
  -- successively with the two cotangent modules.
  have hsq :
      (P.ker • (⊤ : Submodule P.Ring P.ker)).localized' A' U kmap =
        K • (⊤ : Submodule A' K) := by
    rw [Submodule.localized'_smul, Ideal.localized'_eq_map,
      Submodule.localized'_top]
    have hK : K = P.ker.map (algebraMap P.Ring A') := by
      dsimp only [K, locMap]
      exact IsLocalization.ker_map
        (S := A') (Q := S') (g := algebraMap P.Ring S) hT
    rw [hK]
  let qmap := Submodule.toLocalizedQuotient' A' U kmap
      (P.ker • (⊤ : Submodule P.Ring P.ker))
  letI : IsLocalizedModule U qmap :=
    IsLocalizedModule.toLocalizedQuotient' A' U kmap
      (P.ker • (⊤ : Submodule P.Ring P.ker))
  let eTarget :
      (K ⧸
          (P.ker • (⊤ : Submodule P.Ring P.ker)).localized' A' U kmap) ≃ₗ[P.Ring]
        K.Cotangent :=
    (Submodule.quotEquivOfEq _ _ hsq).restrictScalars P.Ring
  let canonical : P.ker.Cotangent →ₗ[P.Ring] K.Cotangent :=
    eTarget.toLinearMap ∘ₗ qmap
  letI : IsLocalizedModule U canonical := by
    dsimp only [canonical]
    exact IsLocalizedModule.of_linearEquiv U qmap eTarget
  have hK : K = P.ker.map (algebraMap P.Ring A') := by
    dsimp only [K, locMap]
    exact IsLocalization.ker_map
      (S := A') (Q := S') (g := algebraMap P.Ring S) hT
  have hQker : K = (P.localization T : Extension R S').ker :=
    hK.trans (ker_eq_map P T).symm
  let eQ : K.Cotangent ≃ₗ[A'] (P.localization T : Extension R S').Cotangent :=
    (Ideal.Cotangent.equivOfEq _ _ hQker).trans
      (P.localization T : Extension R S').cotangentEquivCotangentKer.symm
  let canonicalQ : P.Cotangent →ₗ[P.Ring]
      (P.localization T : Extension R S').Cotangent :=
    (eQ.restrictScalars P.Ring).toLinearMap ∘ₗ canonical ∘ₗ
      P.cotangentEquivCotangentKer.toLinearMap
  letI : IsLocalizedModule U canonicalQ := by
    dsimp only [canonicalQ]
    letI : IsLocalizedModule U
        (canonical ∘ₗ P.cotangentEquivCotangentKer.toLinearMap) :=
      IsLocalizedModule.of_linearEquiv_right U canonical
        P.cotangentEquivCotangentKer
    exact IsLocalizedModule.of_linearEquiv U
      (canonical ∘ₗ P.cotangentEquivCotangentKer.toLinearMap)
      (eQ.restrictScalars P.Ring)
  have qmap_toCotangent (x : P.ker) :
      qmap (P.ker.toCotangent x) = Submodule.Quotient.mk (kmap x) :=
    rfl
  have eTarget_mk (x : K) :
      eTarget (Submodule.Quotient.mk x) = K.toCotangent x := by
    exact Submodule.quotEquivOfEq_mk _ _ hsq x
  have eQ_toCotangent (x : K) :
      (eQ (K.toCotangent x)).val =
        (P.localization T : Extension R S').ker.toCotangent
          (LinearEquiv.ofEq K _ hQker x) := by
    simp only [eQ, LinearEquiv.trans_apply,
      Ideal.Cotangent.equivOfEq_toCotangent]
    rfl
  have hcanonicalQ :
      canonicalQ = (cotangentMap (S' := S') P T).restrictScalars P.Ring := by
    ext x
    obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective x
    apply Extension.Cotangent.ext
    change (eQ (eTarget (qmap (P.ker.toCotangent x)))).val =
      (Extension.Cotangent.map (hom P T) (Extension.Cotangent.mk x)).val
    rw [qmap_toCotangent, eTarget_mk, eQ_toCotangent,
      Extension.Cotangent.map_mk]
    rfl
  have hU : IsLocalizedModule U
      ((cotangentMap (S' := S') P T).restrictScalars P.Ring) := by
    rw [← hcanonicalQ]
    infer_instance

  constructor
  · intro t
    rw [← (Algebra.lsmul S (A := S') S
      (P.localization T : Extension R S').Cotangent).commutes]
    exact (IsLocalization.map_units S' t).map _
  · intro y
    obtain ⟨⟨x, u⟩, hu⟩ := hU.surj y
    change (u : P.Ring) • y = cotangentMap (S' := S') P T x at hu
    refine ⟨⟨x, ⟨algebraMap P.Ring S u, u.2⟩⟩, ?_⟩
    simpa only [Submonoid.smul_def, IsScalarTower.algebraMap_smul] using hu
  · intro x y hxy
    obtain ⟨u, hu⟩ := hU.exists_of_eq hxy
    refine ⟨⟨algebraMap P.Ring S u, u.2⟩, ?_⟩
    simpa only [Submonoid.smul_def, IsScalarTower.algebraMap_smul] using hu

end Algebra.Extension.TargetLocalization
