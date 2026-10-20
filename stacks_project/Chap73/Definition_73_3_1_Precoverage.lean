/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiPrecoverage
public import Mathlib.CategoryTheory.Sites.JointlySurjective
public import Mathlib.CategoryTheory.Sites.MorphismProperty
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap70.Lemma_70_5_1_Points

/-!
# Zariski precoverage on algebraic spaces

The Zariski covering families of algebraic spaces over a scheme `S` are the
jointly surjective families of open immersions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.jointlySurjectivePrecoverage :
  (S : Scheme.{u}) → Precoverage (AlgebraicSpace S))

#check (AlgebraicGeometry.AlgebraicSpace.zariskiPrecoverage :
  (S : Scheme.{u}) → Precoverage (AlgebraicSpace S))

#check (AlgebraicGeometry.AlgebraicSpace.ofArrows_mem_jointlySurjectivePrecoverage_iff :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {I : Type v}
    (X : I → AlgebraicSpace S) (f : ∀ i, X i ⟶ T),
    Presieve.ofArrows X f ∈ jointlySurjectivePrecoverage S T ↔
      (⋃ i, Set.range (Points.map (f i))) = Set.univ)

#check (AlgebraicGeometry.AlgebraicSpace.ofArrows_mem_zariskiPrecoverage_iff :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {I : Type v}
    (X : I → AlgebraicSpace S) (f : ∀ i, X i ⟶ T),
    Presieve.ofArrows X f ∈ zariskiPrecoverage S T ↔
      (∀ i, IsOpenImmersion (f i)) ∧
        (⋃ i, Set.range (Points.map (f i))) = Set.univ)

#check (AlgebraicGeometry.AlgebraicSpace.singleton_mem_zariskiPrecoverage_iff :
  ∀ {S : Scheme.{u}} {X T : AlgebraicSpace S} (f : X ⟶ T),
    Presieve.singleton f ∈ zariskiPrecoverage S T ↔
      IsOpenImmersion f ∧ Function.Surjective (Points.map f))

end AlgebraicGeometry.AlgebraicSpace
