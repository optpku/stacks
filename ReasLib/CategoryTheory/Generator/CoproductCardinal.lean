/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import ReasLib.CategoryTheory.Subobject.Cardinal

@[expose] public section

/-!
# Subobject Cardinals of Constant Coproducts

This module records the cardinal monotonicity used when a family of copies of a generator is
enlarged along an embedding of index types. The statements apply to any object; being a
generator is relevant only to their principal applications.
-/

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasCoproducts.{w} C]

/-- The subobject cardinal of a constant coproduct with `kappa` summands. The cardinal lives in
the coproduct universe, so its chosen representative can be used directly as the index type. -/
@[stacks 079J "cardinal growth function"]
noncomputable abbrev coproductCardinal (G : C) (kappa : Cardinal.{w}) : Cardinal :=
  Cardinal.mk (Subobject (∐ fun _ : kappa.out ↦ G))

/-- Computing `coproductCardinal` with any index type of cardinality `kappa` gives the same
answer. Thus downstream statements do not depend on the representative selected by `kappa.out`. -/
theorem cardinalMk_coprod_const_eq_coproductCardinal
    (G : C) (kappa : Cardinal.{w}) {I : Type w} (hI : Cardinal.mk I = kappa) :
    Cardinal.mk (Subobject (∐ fun _ : I ↦ G)) = coproductCardinal G kappa := by
  classical
  let e : I ≃ kappa.out := (Cardinal.eq.mp (hI.trans (Cardinal.mk_out kappa).symm)).some
  exact cardinalMk_eq_of_iso (Sigma.whiskerEquiv e (fun _ ↦ Iso.refl G))

/-- Equivalent index types give equal subobject cardinals for the corresponding constant
coproducts. -/
theorem cardinalMk_coprod_const_eq_of_equiv (G : C) {I J : Type w} (e : I ≃ J) :
    Cardinal.mk (Subobject (∐ fun _ : I ↦ G)) =
      Cardinal.mk (Subobject (∐ fun _ : J ↦ G)) :=
  cardinalMk_eq_of_iso (Sigma.whiskerEquiv e (fun _ ↦ Iso.refl G))

/-- An embedding of index types induces a subobject-cardinality inequality between the
corresponding constant coproducts. -/
theorem cardinalMk_coprod_const_le_of_embedding (G : C) {I J : Type w} (e : I ↪ J) :
    Cardinal.mk (Subobject (∐ fun _ : I ↦ G)) ≤
      Cardinal.mk (Subobject (∐ fun _ : J ↦ G)) := by
  have hm := MonoCoprod.mono_map'_of_injective (fun _ : J ↦ G) e e.injective
  exact @cardinalMk_le_of_mono _ _ _ _ (Sigma.map' e (fun _ ↦ 𝟙 G)) hm

/-- A cardinal bound on `Subobject X` gives the corresponding bound between constant
coproducts indexed by canonical small representatives. -/
theorem cardinalMk_coprod_const_le_of_cardinalMk_le
    (G : C) {X : C} {kappa : Cardinal.{max u v}}
    [Small.{w} (Subobject X)] [Small.{w} kappa.out]
    (hX : Cardinal.mk (Subobject X) ≤ kappa) :
    Cardinal.mk (Subobject (∐ fun _ : Shrink.{w} (Subobject X) ↦ G)) ≤
      Cardinal.mk (Subobject (∐ fun _ : Shrink.{w} kappa.out ↦ G)) := by
  classical
  let e := (Cardinal.le_def _ _).mp (hX.trans_eq (Cardinal.mk_out kappa).symm)
  exact cardinalMk_coprod_const_le_of_embedding G
    (((equivShrink (Subobject X)).symm.toEmbedding.trans e.some).trans
      (equivShrink kappa.out).toEmbedding)

/-- Enlarging the number of summands can only enlarge `coproductCardinal`. -/
theorem coproductCardinal_mono (G : C) {kappa lambda : Cardinal.{w}}
    (h : kappa ≤ lambda) :
    coproductCardinal G kappa ≤ coproductCardinal G lambda := by
  classical
  exact cardinalMk_coprod_const_le_of_embedding G ((Cardinal.le_def _ _).mp
    (by simpa only [Cardinal.mk_out] using h)).some

end CategoryTheory.Subobject
