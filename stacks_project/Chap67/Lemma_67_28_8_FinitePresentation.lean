/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Finite presentation morphisms of algebraic spaces

A morphism of algebraic spaces is of finite presentation when it is locally of
finite presentation, quasi-compact, and quasi-separated, in the sense of
Stacks Definition 67.28.1 (3).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentation :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentation.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, FinitePresentation (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentation.of_isIso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [IsIso f] → FinitePresentation f)

#check
  (AlgebraicGeometry.AlgebraicSpace.FinitePresentation.instOfLocallyOfFinitePresentationQuasiCompactQuasiSeparated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [LocallyOfFinitePresentation f] → [QuasiCompact f] → [QuasiSeparated f] →
        FinitePresentation f)

end AlgebraicGeometry.AlgebraicSpace
