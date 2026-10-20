/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

/- Lemma 35.25.5: if the inverse image of a closed subset is proper over every member of
an fpqc covering family, then the closed subset is proper over the base. -/
@[stacks 0F4J] #check
  (AlgebraicGeometry.ClosedSubset.IsProperOver.of_fpqcCovering :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      (Z : TopologicalSpace.Closeds X) {ι : Type v}
      (family : ι → Over Y), AlgebraicGeometry.Scheme.FpqcCovering family →
      (∀ i : ι,
        AlgebraicGeometry.ClosedSubset.IsProperOver (pullback.snd f (family i).hom)
          (Z.preimage (pullback.fst f (family i).hom).continuous)) →
      AlgebraicGeometry.ClosedSubset.IsProperOver f Z)
