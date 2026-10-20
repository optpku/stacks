/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.IntegralImage
public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap72.Lemma_72_4_7_IntegralClosed

/-! Compatibility checks for integral images of closed subspaces. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.integralGenericPoint :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} → (Z : ClosedSubspace X) →
    [IsIntegral Z.X] → Points Z.X)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.integralImage :
  {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → [IsDecent Y] →
    (Z : ClosedSubspace X) → [IsIntegral Z.X] → (X ⟶ Y) → ClosedSubspace Y)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.isGenericPoint_integralGenericPoint :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsIntegral Z.X],
    IsGenericPoint (integralGenericPoint Z) (Set.univ : Set (Points Z.X)))

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.integralImage_spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (Z : ClosedSubspace X) [IsIntegral Z.X] (f : X ⟶ Y),
    IsIntegral (Z.integralImage f).X ∧
      IsGenericPoint (Points.map (Z.ι ≫ f) (integralGenericPoint Z))
        (Z.integralImage f).pointsSet ∧
      (Z.integralImage f).pointsSet =
        closure {Points.map (Z.ι ≫ f) (integralGenericPoint Z)})

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.pointsSet_integralImage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (Z : ClosedSubspace X) [IsIntegral Z.X] (f : X ⟶ Y),
    (Z.integralImage f).pointsSet =
      closure {Points.map (Z.ι ≫ f) (integralGenericPoint Z)})

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.isGenericPoint_integralImage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (Z : ClosedSubspace X) [IsIntegral Z.X] (f : X ⟶ Y),
    IsGenericPoint (Points.map (Z.ι ≫ f) (integralGenericPoint Z))
      (Z.integralImage f).pointsSet)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.existsUnique_hom_integralImage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (Z : ClosedSubspace X) [IsIntegral Z.X] (f : X ⟶ Y),
    ∃! g : Z.X ⟶ (Z.integralImage f).X,
      g ≫ (Z.integralImage f).ι = Z.ι ≫ f)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.unique_integralImage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (Z : ClosedSubspace X) [IsIntegral Z.X] (f : X ⟶ Y)
    (W : ClosedSubspace Y) [IsIntegral W.X]
    (h_factor : ∃ g : Z.X ⟶ W.X, g ≫ W.ι = Z.ι ≫ f ∧ Dominant g),
    ∃! φ : W.X ⟶ (Z.integralImage f).X, φ ≫ (Z.integralImage f).ι = W.ι)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.dominant_hom_integralImage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent Y] (Z : ClosedSubspace X) [IsIntegral Z.X] (f : X ⟶ Y)
    {g : Z.X ⟶ (Z.integralImage f).X}
    (hg : g ≫ (Z.integralImage f).ι = Z.ι ≫ f),
    Dominant g)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.proper_hom_integralImage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Proper f] (Z : ClosedSubspace X) [IsIntegral Z.X]
    (Z' : ClosedSubspace Y) [IsIntegral Z'.X] (g : Z.X ⟶ Z'.X)
    (hg : g ≫ Z'.ι = Z.ι ≫ f) (h_dom : Dominant g),
    Proper g)

#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.surjective_hom_integralImage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Proper f] (Z : ClosedSubspace X) [IsIntegral Z.X]
    (Z' : ClosedSubspace Y) [IsIntegral Z'.X] (g : Z.X ⟶ Z'.X)
    (hg : g ≫ Z'.ι = Z.ι ≫ f) (h_dom : Dominant g),
    Surjective g)
