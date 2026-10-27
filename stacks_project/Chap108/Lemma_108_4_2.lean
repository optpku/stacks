/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.LocallyOfFinitePresentation
import StacksCheckRecall

/-!
# Lemma 108.4.2

The structure morphism of the stack of coherent sheaves over `B` is
quasi-separated and locally of finite presentation.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.4.2 (1): the structure morphism of the stack of coherent
sheaves is quasi-separated. -/
@[stacks 0DLZ] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.instQuasiSeparated_forget :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] [Separated f],
    AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.QuasiSeparated (AlgebraicGeometry.AlgebraicSpace.CohStack.forget f))

/- Lemma 108.4.2 (2): the structure morphism of the stack of coherent
sheaves is locally of finite presentation. -/
@[stacks 0DLZ] #check (AlgebraicGeometry.AlgebraicSpace.CohStack.instLocallyOfFinitePresentation_forget :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] [Separated f],
    AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.LocallyOfFinitePresentation (AlgebraicGeometry.AlgebraicSpace.CohStack.forget f))
