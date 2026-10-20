/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.FiberCriterion

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.16.3 (1): a morphism between locally Noetherian schemes is flat if its
composite to the base and all its induced morphisms on fibres are flat. -/
@[stacks 039D] #check
  (AlgebraicGeometry.Scheme.Hom.FlatnessByFibers.of_isLocallyNoetherian :
    ∀ {S X Y : Scheme.{u}}
      [IsLocallyNoetherian S] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
      (f : X ⟶ Y) (g : Y ⟶ S) [Flat (f ≫ g)]
      [∀ s : S, Flat (compFiberToBaseFiber f g s)],
      Flat f)

/- Lemma 37.16.3 (2): if the morphism in the fibrewise flatness criterion is also
surjective, then its locally Noetherian target is flat over the base. -/
@[stacks 039D] #check
  (AlgebraicGeometry.Scheme.Hom.FlatnessByFibers.base_of_surjective_of_isLocallyNoetherian :
    ∀ {S X Y : Scheme.{u}}
      [IsLocallyNoetherian S] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
      (f : X ⟶ Y) (g : Y ⟶ S) [Flat (f ≫ g)]
      [∀ s : S, Flat (compFiberToBaseFiber f g s)] [Surjective f],
      Flat g)

end AlgebraicGeometry.Scheme.Hom
