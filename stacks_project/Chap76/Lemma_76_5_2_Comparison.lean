/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_9_Lift
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_13_1
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf
public import stacks_project.Chap67.Remark_67_12_4_Coborder
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap76.Definition_76_6_5_Conormal

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Etale

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.restrictEtale :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ],
    (Modules.pullback (Hom.Conormal.toZ i φ)).obj (Hom.conormalSheaf i) ≅
      Hom.conormalSheaf (Hom.Conormal.ι i φ))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.coborderHom_range_subset :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ],
    Set.range (Points.map ((IsImmersion.coborderRange (Hom.Conormal.ι i φ)).ι ≫ φ)) ⊆
      Set.range (Points.map (IsImmersion.coborderRange i).ι))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.chartCoborderHom_range_subset :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ] (f : ofOver U ⟶ ofOver V)
    (hf : f ≫ ψ = φ),
    Set.range (Points.map ((IsImmersion.coborderRange (Hom.Conormal.ι i φ)).ι ≫ f)) ⊆
      Set.range (Points.map (IsImmersion.coborderRange (Hom.Conormal.ι i ψ)).ι))

