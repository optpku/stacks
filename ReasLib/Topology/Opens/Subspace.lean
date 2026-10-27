/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Opens.Inclusion
public import Mathlib.Topology.Sheaves.Over

/-!
# Subspace opens and their ambient representatives

This module owns the bidirectional passage between opens of an open subspace `U` and ambient opens
of `X` that are contained in `U`. The key constructions are:

- `subspaceOpenOfLE`: embed `W ≤ U` as an open of the subspace `U`
- `ambientOpenOfSubspaceOpen`: recover the canonical ambient representative
- `subspaceInclusionFunctor`: the functor from opens of the subspace to ambient opens

These form an equivalence (via `Opens.overEquivalence`) used pervasively by restriction,
pushforward, and section-comparison APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open TopologicalSpace.Opens

noncomputable section

universe w

namespace TopCat.Opens.Subspace

variable {X : TopCat.{w}}

/-- The ambient open `W ⊆ U`, regarded as an open of the open subspace `U`. -/
def subspaceOpenOfLE {W U : Opens X} (h : W ≤ U) : Opens (space U) :=
  U.overEquivalence.functor.obj (Over.mk (CategoryTheory.homOfLE h))

/-- The canonical ambient open representing an open of the open subspace `U`. -/
abbrev ambientOpenOfSubspaceOpen {U : Opens X} (V : Opens (space U)) : Opens X :=
  (U.overEquivalence.inverse.obj V).left

/-- The canonical ambient representative of a subspace open is contained in `U`. -/
abbrev ambientOpenOfSubspaceOpen_le {U : Opens X} (V : Opens (space U)) :
    ambientOpenOfSubspaceOpen V ≤ U :=
  (U.overEquivalence.inverse.obj V).hom.le

/-- Reinterpreting the canonical ambient representative as a subspace open recovers the
original open. -/
noncomputable abbrev subspaceOpenOfAmbientOpenIso {U : Opens X}
    (V : Opens (space U)) :
    subspaceOpenOfLE (ambientOpenOfSubspaceOpen_le V) ≅ V :=
  U.overEquivalence.counitIso.app V

/-- An inclusion `A ≤ B ≤ U` induces a morphism between the represented opens of `U`. -/
def subspaceOpenHom {A B U : Opens X}
    (hA : A ≤ U) (hB : B ≤ U) (hAB : A ≤ B) :
    subspaceOpenOfLE hA ⟶ subspaceOpenOfLE hB :=
  U.overEquivalence.functor.map
    (Over.homMk (CategoryTheory.homOfLE hAB) (Subsingleton.elim _ _))

/-- The morphism induced by a reflexive inclusion is the identity. -/
@[simp] theorem subspaceOpenHom_refl {W U : Opens X} (hWU : W ≤ U) :
    subspaceOpenHom hWU hWU (le_refl W) = 𝟙 _ :=
  Subsingleton.elim _ _

/-- The inclusion functor from opens of the subspace to ambient opens. -/
abbrev subspaceInclusionFunctor (U : Opens X) : Opens (space U) ⥤ Opens X :=
  (Opens.isOpenEmbedding U).functor

/-- The `Over`-equivalence for `U` remembers the ambient open that produced a subspace open. -/
theorem overEquivalenceFunctorObjEq (U : Opens X) (V : Over U) :
    (subspaceInclusionFunctor U).obj (U.overEquivalence.functor.obj V) = V.left := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, V.hom.le hx⟩, hx, rfl⟩

/-- Including the subspace open represented by `W ≤ U` back into `X` recovers `W`. -/
theorem subspaceOpenOfLE_image_eq {W U : Opens X} (h : W ≤ U) :
    (subspaceInclusionFunctor U).obj (subspaceOpenOfLE h) = W :=
  overEquivalenceFunctorObjEq U (Over.mk (CategoryTheory.homOfLE h))

/-- After identifying represented subspace opens with ambient opens, the inclusion functor sends
`subspaceOpenHom` to the ambient inclusion. -/
theorem subspaceInclusionFunctor_map_subspaceOpenHom
    {W V U : Opens X} (hWU : W ≤ U) (hVU : V ≤ U) (hWV : W ≤ V) :
    eqToHom (subspaceOpenOfLE_image_eq hWU).symm ≫
        (subspaceInclusionFunctor U).map (subspaceOpenHom hWU hVU hWV) =
      CategoryTheory.homOfLE hWV ≫ eqToHom (subspaceOpenOfLE_image_eq hVU).symm :=
  Subsingleton.elim _ _

/-- Every open of an open subspace is represented by an ambient open contained in `U`. -/
theorem exists_subspaceOpenOfLE_eq {U : Opens X} (V : Opens (space U)) :
    ∃ W : Opens X, ∃ hW : W ≤ U, subspaceOpenOfLE hW = V :=
  ⟨ambientOpenOfSubspaceOpen V, ambientOpenOfSubspaceOpen_le V,
    le_antisymm (subspaceOpenOfAmbientOpenIso V).hom.le
      (subspaceOpenOfAmbientOpenIso V).inv.le⟩

/-- Membership in a subspace open is membership of the underlying point in its ambient image. -/
theorem mem_subspaceOpen_iff {U : Opens X} (A : Opens (space U)) (x : space U) :
    x ∈ A ↔ x.1 ∈ (subspaceInclusionFunctor U).obj A := by
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    exact (Subtype.ext hxy : y = x) ▸ hy

/-- Membership in `subspaceOpenOfLE h` is membership in the ambient open. -/
theorem mem_subspaceOpenOfLE_iff {W U : Opens X} (h : W ≤ U) (x : space U) :
    x ∈ subspaceOpenOfLE h ↔ x.1 ∈ W :=
  Iff.rfl

/-- The represented open of `A ⊓ B` is the intersection of the represented opens. -/
@[simp] theorem subspaceOpenOfLE_inf {A B D : Opens X} (hAD : A ≤ D) (hBD : B ≤ D) :
    subspaceOpenOfLE (inf_le_left.trans hAD : A ⊓ B ≤ D) =
      subspaceOpenOfLE hAD ⊓ subspaceOpenOfLE hBD := rfl

/-- Points of `W` land in the represented open `W ⊆ U` under the inclusion `W ↪ U`. -/
theorem homOfLE_mem_subspaceOpenOfLE {W U : Opens X} (h : W ≤ U) (x : space W) :
    homOfLE h x ∈ subspaceOpenOfLE h :=
  x.2

/-- Pulling a represented open back along an inclusion preserves its ambient representative. -/
theorem homOfLE_functor_obj_subspaceOpenOfLE
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C) :
    (homOfLE_isOpenEmbedding hBC).functor.obj (subspaceOpenOfLE hAB) =
      subspaceOpenOfLE (hAB.trans hBC) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x.1, hAB hx⟩, hx, Subtype.ext rfl⟩

end TopCat.Opens.Subspace

end

end
