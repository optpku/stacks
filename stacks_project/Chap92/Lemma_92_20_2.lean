/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap92.Definition_92_20_1_Morphism
public import stacks_project.Chap92.Lemma_92_18_6_HomologyZero
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex.HomologyZero
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

universe u

/-!
# Degree-zero homology of the cotangent complex of a morphism of ringed spaces

Lemma 92.20.2 identifies `H^0(L[f])` with the sheaf of relative differentials `Ω[f]`
for a morphism of ringed spaces.
-/

/- Lemma 92.20.2
Let `f : (X, O_X) ⟶ (S, O_S)` be a morphism of ringed spaces. Then
`H^0(L_{X/S}) = Ω_{X/S}`.
-/
@[stacks 08UV] #check (AlgebraicGeometry.RingedSpace.homologyZeroIso :
  ∀ {X S : AlgebraicGeometry.RingedSpace.{u}} (f : X ⟶ S),
    (AlgebraicGeometry.RingedSpace.cotangentComplex f).homology 0 ≅
      AlgebraicGeometry.RingedSpace.Hom.differentials f)
