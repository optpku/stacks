/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Algebra.Category.Grp.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import ReasLib.AlgebraicGeometry.GroupoidsOver.PresheafPullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small

/-!
# Pullback and small étale restriction of sheaves on groupoid fibrations

An object over a scheme determines inverse image on its big standard sites.
For abelian sheaves in the étale topology, continuous restriction further gives
a sheaf on its small étale site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor

noncomputable section

universe u a b

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {𝒳 : GroupoidsOver S}

/-- The inverse-image sheaf `x⁻¹ F` on `(Sch/U)_τ`, with `U = p(x)`, obtained by
packaging `pullbackPresheaf x F.obj`. -/
def pullbackSheaf {A : Type a} [Category.{b} A] (τ : StandardTopology)
    (x : 𝒳.total) (F : Sheaf (𝒳.associatedTopology τ) A) :
    Sheaf (τ.overTopology (𝒳.p.obj x).left) A where
  obj := pullbackPresheaf x F.obj
  property := sorry

/-- The underlying presheaf of `pullbackSheaf τ x F` is `pullbackPresheaf x F.obj`. -/
theorem pullbackSheaf_obj {A : Type a} [Category.{b} A] (τ : StandardTopology)
    (x : 𝒳.total) (F : Sheaf (𝒳.associatedTopology τ) A) :
    (pullbackSheaf τ x F).obj = pullbackPresheaf x F.obj :=
  sorry

/-- `pullbackSheaf` is presheaf inverse image of `F` along `yonedaEval x`. -/
theorem pullbackSheaf_eq {A : Type a} [Category.{b} A] (τ : StandardTopology)
    (x : 𝒳.total) (F : Sheaf (𝒳.associatedTopology τ) A) :
    (pullbackSheaf τ x F).obj = (presheafInverseImage (yonedaEval x) A).obj F.obj :=
  sorry


/-- Restriction of an étale sheaf `F` on `𝒳` to the small étale site of
`U = p(x)`, as the small-to-big inverse image of `pullbackSheaf .etale x F`. -/
def restrictEtaleSheaf (x : 𝒳.total)
    (F : Sheaf 𝒳.etaleTopology AddCommGrpCat.{u}) :
    Sheaf ((𝒳.p.obj x).left.smallEtaleTopology) AddCommGrpCat.{u} :=
  ((Scheme.Etale.SmallToBig.relocalizationFunctor (𝟙 (𝒳.p.obj x).left)).sheafPushforwardContinuous
      AddCommGrpCat.{u} ((𝒳.p.obj x).left.smallEtaleTopology)
      (StandardTopology.etale.overTopology (𝒳.p.obj x).left)).obj
    (pullbackSheaf .etale x F)

/-- The underlying presheaf of `restrictEtaleSheaf x F` is
`restrictSmallEtale x F.obj`. -/
theorem restrictEtaleSheaf_obj (x : 𝒳.total)
    (F : Sheaf 𝒳.etaleTopology AddCommGrpCat.{u}) :
    (restrictEtaleSheaf x F).obj = restrictSmallEtale x F.obj :=
  sorry

/-- `restrictEtaleSheaf x F` is the small-to-big inverse image of
`pullbackSheaf .etale x F`. -/
theorem restrictEtaleSheaf_eq (x : 𝒳.total)
    (F : Sheaf 𝒳.etaleTopology AddCommGrpCat.{u}) :
    restrictEtaleSheaf x F =
      ((Scheme.Etale.SmallToBig.relocalizationFunctor
          (𝟙 (𝒳.p.obj x).left)).sheafPushforwardContinuous
          AddCommGrpCat.{u} ((𝒳.p.obj x).left.smallEtaleTopology)
          (StandardTopology.etale.overTopology (𝒳.p.obj x).left)).obj
        (pullbackSheaf .etale x F) :=
  sorry


end AlgebraicGeometry.GroupoidsOver
