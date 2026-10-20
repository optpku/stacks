module

public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FinitePresentation

/-!
# Finite presentation morphisms of algebraic stacks

A morphism of algebraic stacks is of finite presentation when it is locally
of finite presentation, quasi-compact, and quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.FinitePresentation :
  {S : Scheme.{u}} → {X Y : GroupoidsOver S} →
    [AlgebraicStack X] → [AlgebraicStack Y] → (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.FinitePresentation.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [FinitePresentation f],
    LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f)

#check (AlgebraicGeometry.AlgebraicStack.FinitePresentation.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    FinitePresentation (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.FinitePresentation.of_isIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f],
    FinitePresentation f)

#check (AlgebraicGeometry.AlgebraicStack.FinitePresentation.instOfLocallyOfFinitePresentationQuasiCompactQuasiSeparated :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f],
    FinitePresentation f)

#check (AlgebraicGeometry.AlgebraicStack.FinitePresentation.of_toGroupoids :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.FinitePresentation f],
    FinitePresentation (AlgebraicSpace.toGroupoids.map f))

end AlgebraicGeometry.AlgebraicStack
