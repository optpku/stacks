/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AtlasCharts
public import Mathlib.CategoryTheory.Sites.LocallySurjective

@[expose] public section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Smallness

/-- Étale coverings are fppf coverings. -/
theorem etale_le_fppf : Scheme.etaleTopology.{u} ≤ Scheme.fppfTopology :=
  Precoverage.toGrothendieck_mono
    (Scheme.precoverage_mono fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩)

/-- An algebraic space's supplied fppf sheaf is also an étale sheaf. -/
theorem etaleSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.etaleTopology.over S) X.functorOfPoints :=
  Presheaf.IsSheaf.of_le (fun U R h ↦ etale_le_fppf _ h) X.isSheaf

/-- A map out of an algebraic space is determined on its given atlas. -/
theorem atlas_cancel {S : Scheme.{u}} (X Y : AlgebraicSpace S) (f g : X ⟶ Y)
    (h : atlasMap X ≫ f = atlasMap X ≫ g) : f = g := by
  -- Local instance justification (proof-local temporary data): imageSieve_mem must use local surjectivity of this supplied atlas map.
  letI : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (atlasMap X) :=
    atlasMap_surjective X
  change (f : X.functorOfPoints ⟶ Y.functorOfPoints) = g
  apply NatTrans.ext
  funext U
  ext x
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 (etaleSheaf Y)).isSeparated _
    (Presheaf.imageSieve_mem (Scheme.etaleTopology.over S) (atlasMap X) x)).ext
  rintro V k ⟨s, hs⟩
  have hf := ConcreteCategory.congr_hom (f.naturality k.op) x
  have hg := ConcreteCategory.congr_hom (g.naturality k.op) x
  dsimp at hf hg ⊢
  rw [← hf, ← hg, ← hs]
  exact ConcreteCategory.congr_hom (congr_app h (op V)) s

/-- The small set of atlas sections records every morphism. -/
def atlasEvaluation {S : Scheme.{u}} (X Y : AlgebraicSpace S) (f : X ⟶ Y) :
    Y.functorOfPoints.obj (op (atlasOver X)) := yonedaEquiv (atlasMap X ≫ f)

/-- Atlas evaluation is injective, with a complete proof. -/
theorem atlasEvaluation_injective {S : Scheme.{u}} (X Y : AlgebraicSpace S) :
    Function.Injective (atlasEvaluation X Y) := by
  intro f g h
  apply atlas_cancel X Y f g
  exact yonedaEquiv.injective h

/-- Algebraic-space Hom sets are small by the actual atlas-evaluation injection. -/
instance locallySmall {S : Scheme.{u}} : LocallySmall.{u} (AlgebraicSpace S) where
  hom_small X Y := small_of_injective (atlasEvaluation_injective X Y)


end AlgebraicGeometry.AlgebraicSpace.Smallness
