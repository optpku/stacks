/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Representability
import StacksCheckRecall

/-!
# Lemma 108.10.2

The structure morphism of the functor of relative morphisms `Mor_B(Y, X)`
over `B` is separated and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

/- Lemma 108.10.2 (1): the structure morphism of Mor_B(Y, X) ⟶ B is
separated. -/
@[stacks 0DPN] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativeHom.instIsSeparatedOver :
    ∀ {S : Scheme.{u}} {Y B X : AlgebraicSpace S} (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x], Quot.IsSeparatedOver (mor y x))

/- Lemma 108.10.2 (2): the structure morphism of Mor_B(Y, X) ⟶ B is
locally of finite presentation. -/
@[stacks 0DPN] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativeHom.mor_isLocallyOfFinitePresentationOver :
    ∀ {S : Scheme.{u}} {Y B X : AlgebraicSpace S} (y : Y ⟶ B) (x : X ⟶ B)
    [FinitePresentation x] [Separated x] [FinitePresentation y] [Flat y]
    [Proper y], IsLocallyOfFinitePresentationOver (mor y x))

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
