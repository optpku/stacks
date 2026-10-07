module

public import ReasLib.Topology.Sheaves.OpenSubset
public import ReasLib.Topology.Sheaves.Pullback.Composition

/-!
# Sheaf restriction along open-subspace inclusions

This module owns composition comparisons for the `Topology.IsOpenEmbedding.sheafPullback` model
of restriction along the canonical inclusions of open subspaces.  Unlike
`TopCat.Sheaf.pullback`, this model is available for an arbitrary coefficient category, so it is
the appropriate common layer for open-cover descent data.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe w v

namespace TopCat.Opens.Subspace

variable {X : TopCat.{w}}

/-- Restriction of `C`-valued sheaves along the canonical inclusion of open subspaces induced by
`W ≤ U`. -/
abbrev sheafPullback (C : Type v) [Category.{w} C] {W U : Opens X} (h : W ≤ U) :
    TopCat.Sheaf C (space U) ⥤ TopCat.Sheaf C (space W) :=
  (homOfLE_isOpenEmbedding h).sheafPullback C

/-- The image-open functors of nested open-subspace inclusions compose to the direct inclusion. -/
theorem openEmbeddingFunctor_comp
    {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    (homOfLE_isOpenEmbedding hTW).functor ⋙ (homOfLE_isOpenEmbedding hWU).functor =
      (homOfLE_isOpenEmbedding (hTW.trans hWU)).functor := sorry

/-- Pullback of `C`-valued sheaves through nested open-subspace inclusions agrees with direct
restriction. -/
noncomputable def sheafPullbackCompIso
    {C : Type v} [Category.{w} C] {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    sheafPullback C hWU ⋙ sheafPullback C hTW ≅ sheafPullback C (hTW.trans hWU) :=
  Functor.sheafPushforwardContinuousComp'
    (F := (homOfLE_isOpenEmbedding hTW).functor)
    (G := (homOfLE_isOpenEmbedding hWU).functor)
    (FG := (homOfLE_isOpenEmbedding (hTW.trans hWU)).functor)
    (eFG := eqToIso (openEmbeddingFunctor_comp hTW hWU))
    C
    (Opens.grothendieckTopology (space T))
    (Opens.grothendieckTopology (space W))
    (Opens.grothendieckTopology (space U))

/-- The image-open functor through an open subspace agrees with the direct ambient inclusion. -/
theorem openEmbeddingFunctor_comp_inclusion
    {W U : Opens X} (h : W ≤ U) :
    (homOfLE_isOpenEmbedding h).functor ⋙ U.isOpenEmbedding.functor =
      W.isOpenEmbedding.functor := sorry

/-- Pullback of `C`-valued sheaves from `X` to `U` and then to `W ⊆ U` agrees with direct
restriction to `W`. -/
noncomputable def sheafPullbackCompInclusionIso
    {C : Type v} [Category.{w} C] {W U : Opens X} (h : W ≤ U) :
    (U.isOpenEmbedding.sheafPullback C) ⋙ sheafPullback C h ≅
      (W.isOpenEmbedding.sheafPullback C) :=
  Functor.sheafPushforwardContinuousComp'
    (F := (homOfLE_isOpenEmbedding h).functor)
    (G := U.isOpenEmbedding.functor)
    (FG := W.isOpenEmbedding.functor)
    (eFG := eqToIso (openEmbeddingFunctor_comp_inclusion h))
    C
    (Opens.grothendieckTopology (space W))
    (Opens.grothendieckTopology (space U))
    (Opens.grothendieckTopology X)

end TopCat.Opens.Subspace
