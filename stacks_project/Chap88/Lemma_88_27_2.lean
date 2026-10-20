/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.FullyFaithful
public import stacks_project.Chap88.«88_27_0_1»
import StacksCheckRecall

/-!
# Completion is fully faithful on locally finite-type morphisms isomorphic over U

In the standing locally Noetherian setup, completing along `T` induces a
bijection on slice Hom-sets, so the completion functor is fully faithful.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

/- Lemma 88.27.2: completion induces a bijection on morphisms over the base
from a locally Noetherian algebraic space to a locally finite-type algebraic
space isomorphic over the open complement. -/
@[stacks 0GDR] #check (AlgebraicGeometry.AlgebraicSpace.completionAlong.homMap_bijective :
  ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (T : Closeds (Points X))
    (f : X' ⟶ X) [LocallyOfFiniteType f]
    [IsIso (openInverseImageTo f (openComplementι X T))] (g : Y ⟶ X),
    Function.Bijective
      (fun (φ : Over.mk g ⟶ Over.mk f) ↦ completionAlong.homMap T φ))

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.functor_map_bijective :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]
    (T : Closeds (Points X)) {Y Y' : completionAlong.Source X T},
    Function.Bijective (fun (φ : Y ⟶ Y') ↦ (completionFunctor X T).map φ))

