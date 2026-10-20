/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.FiberCriterion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.16.4 (1): for composable scheme morphisms `f : X ⟶ Y` and
`g : Y ⟶ S`, if `f ≫ g` is locally of finite presentation and flat, every
induced fibre morphism is flat, and `g` is locally of finite type, then `f` is
flat. -/
@[stacks 039E] #check
  (AlgebraicGeometry.Scheme.Hom.FlatnessByFibers.of_finitePresentation :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [LocallyOfFinitePresentation (f ≫ g)] [Flat (f ≫ g)]
      [∀ s : S, Flat (compFiberToBaseFiber f g s)] [LocallyOfFiniteType g],
      Flat f)

/- Lemma 37.16.4 (2): under the hypotheses of part (1), if `f` is surjective,
then the base morphism `g : Y ⟶ S` is flat. -/
@[stacks 039E] #check
  (AlgebraicGeometry.Scheme.Hom.FlatnessByFibers.base_of_surjective_of_finitePresentation :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [LocallyOfFinitePresentation (f ≫ g)] [Flat (f ≫ g)]
      [∀ s : S, Flat (compFiberToBaseFiber f g s)] [LocallyOfFiniteType g]
      [Surjective f],
      Flat g)

end AlgebraicGeometry.Scheme.Hom
