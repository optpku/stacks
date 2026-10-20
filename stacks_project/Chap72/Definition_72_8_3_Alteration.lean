/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Alteration
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Alteration
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap72.Definition_72_4_1_Integral

/-!
# Alterations of integral algebraic spaces

An alteration is a proper dominant morphism of integral algebraic spaces that
is finite over some nonempty open subspace of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.IsAlteration :
  ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S} [IsIntegral Y] [IsIntegral X],
    (Y ⟶ X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isAlteration_iff :
  ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    [IsIntegral Y] [IsIntegral X] (f : Y ⟶ X),
    IsAlteration f ↔
      Proper f ∧ Dominant f ∧
        ∃ U : OpenSubspace X, U.pointsSet.Nonempty ∧
          IsFinite (pullback.snd f U.ι))

#check (AlgebraicGeometry.AlgebraicSpace.instIsAlteration_id :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsIntegral X],
    IsAlteration (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.instIsAlteration_ofOverMap :
  ∀ {S : Scheme.{u}} {U V : Over S}
    (f : U ⟶ V) [AlgebraicGeometry.IsIntegral U.left]
    [AlgebraicGeometry.IsIntegral V.left]
    [AlgebraicGeometry.IsAlteration f.left],
    IsAlteration (ofOverMap f))

end AlgebraicGeometry.AlgebraicSpace
