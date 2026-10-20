/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
import StacksCheckRecall

/-!
# Separation axioms for morphisms of algebraic stacks

A morphism of algebraic stacks is DM, quasi-DM, separated, or quasi-separated
according as its relative 2-diagonal is unramified, locally quasi-finite,
proper, or both quasi-compact and quasi-separated, tested on scheme-slice
representing morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

/- Definition 101.4.1 (1): a morphism of algebraic stacks is DM if its
relative 2-diagonal is unramified. -/
@[stacks 04YW] #check (AlgebraicGeometry.AlgebraicStack.DM :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)

/- Definition 101.4.1 (2): a morphism of algebraic stacks is quasi-DM if its
relative 2-diagonal is locally quasi-finite. -/
@[stacks 04YW] #check (AlgebraicGeometry.AlgebraicStack.QuasiDM :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)

/- Definition 101.4.1 (3): a morphism of algebraic stacks is separated if its
relative 2-diagonal is proper. -/
@[stacks 04YW] #check (AlgebraicGeometry.AlgebraicStack.Separated :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)

/- Definition 101.4.1 (4): a morphism of algebraic stacks is quasi-separated if
its relative 2-diagonal is quasi-compact and quasi-separated. -/
@[stacks 04YW] #check (AlgebraicGeometry.AlgebraicStack.QuasiSeparated :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.DM.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    DM (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.DM.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [DM f],
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
      (Hom.diagonal.{u + 1, u, u + 1} f))

#check (AlgebraicGeometry.AlgebraicStack.QuasiDM.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    QuasiDM (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.QuasiDM.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiDM f],
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
      (Hom.diagonal.{u + 1, u, u + 1} f))

#check (AlgebraicGeometry.AlgebraicStack.Separated.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    Separated (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.Separated.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Separated f],
    Groupoids.Hom.has (@AlgebraicSpace.Proper S)
      (Hom.diagonal.{u + 1, u, u + 1} f))

#check (AlgebraicGeometry.AlgebraicStack.QuasiSeparated.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    QuasiSeparated (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.QuasiSeparated.iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    QuasiSeparated f ↔
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
          (Hom.diagonal.{u + 1, u, u + 1} f) ∧
        Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
          (Hom.diagonal.{u + 1, u, u + 1} f))

#check (AlgebraicGeometry.AlgebraicStack.QuasiSeparated.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiSeparated f],
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
        (Hom.diagonal.{u + 1, u, u + 1} f) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} f))

#check (AlgebraicGeometry.AlgebraicStack.relativelyRepresentable_diagonal :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    relativelyRepresentableByAlgebraicSpaces
      (Hom.diagonal.{u + 1, u, u + 1} f))

end AlgebraicGeometry.AlgebraicStack
