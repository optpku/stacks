/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension.DenseOpen
import StacksCheckRecall

/-!
# Extending relative-dimension bounds from a dense open

A relative-dimension bound for a flat morphism of algebraic spaces locally of
finite type extends from a topologically dense open of the target when the
morphism is locally of finite presentation or the open inclusion is
quasi-compact.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.37.3: a flat morphism of algebraic spaces locally of finite type
has relative dimension at most `d` if it has that bound after base change to a
topologically dense open subspace, and either the morphism is locally of finite
presentation or the open inclusion is quasi-compact. -/
@[stacks 0878]
#check (AlgebraicGeometry.AlgebraicSpace.RelativeDimensionLE.of_restrict_of_flat :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f] (V : OpenSubspace Y) (d : ℕ)
    (hV_dense : Dense V.pointsSet)
    [RelativeDimensionLE (pullback.snd f V.ι) d]
    (h_finitePresentation_or_quasiCompact :
      LocallyOfFinitePresentation f ∨ QuasiCompact V.ι),
    RelativeDimensionLE f d)
