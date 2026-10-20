/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.Flat
import StacksCheckRecall

/-!
# Finite locally free morphisms of algebraic spaces versus finite, flat, and
locally of finite presentation

A morphism of algebraic spaces is finite locally free if and only if it is
finite, flat, and locally of finite presentation. Over a locally Noetherian
target, finite plus flat is equivalent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.46.6 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is finite locally free if and only if `f`
is finite, flat, and locally of finite presentation. -/
@[stacks 0416] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree.iff_isFinite_and_flat_and_locallyOfFinitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      FiniteLocallyFree f ↔ IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f)

/- Lemma 67.46.6 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `Y` is locally Noetherian, then `f` is finite
locally free if and only if `f` is finite and flat. -/
@[stacks 0416] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree.iff_isFinite_and_flat :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsLocallyNoetherian Y],
      FiniteLocallyFree f ↔ IsFinite f ∧ Flat f)

end AlgebraicGeometry.AlgebraicSpace
