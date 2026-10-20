/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Composition

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- The composite of flat scheme morphisms is flat. -/
#check (AlgebraicGeometry.Flat.comp :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g], Flat (f ≫ g))

/- Relative dimensions add under composition when the first morphism is flat. -/
#check (AlgebraicGeometry.Scheme.Hom.relativeDimension_comp_of_flat :
  ∀ {X Y Z : Scheme.{u}} {r s : ℕ} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Scheme.Hom.RelativeDimension f r] [Scheme.Hom.RelativeDimension g s] [Flat f],
    Scheme.Hom.RelativeDimension (f ≫ g) (r + s))

/- Lemma 42.14.3: for flat morphisms of relative dimensions `r` and `s`, successive
pullback of cycles equals pullback along their composite after the canonical degree transport. -/
@[stacks 02RD] #check (AlgebraicGeometry.CycleGroup.flatPullback_comp :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X Y Z : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z) (r s : ℕ) [Flat f.left] [Flat g.left]
    [Scheme.Hom.RelativeDimension f.left r] [Scheme.Hom.RelativeDimension g.left s]
    (k : ℤ),
    (AlgebraicGeometry.CycleGroup.reindex (X.hom.relativeDimensionFunction delta)
        (AlgebraicGeometry.CycleGroup.flatPullback_comp_degree k r s)).comp
        ((AlgebraicGeometry.CycleGroup.flatPullback delta X Y f r (k + (s : ℤ))).comp
          (AlgebraicGeometry.CycleGroup.flatPullback delta Y Z g s k)) =
      AlgebraicGeometry.CycleGroup.flatPullback delta X Z (f ≫ g) (r + s) k)
