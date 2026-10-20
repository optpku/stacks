/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 29.48.1

The reusable finite-locally-free scheme-morphism owner is maintained in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic`.
-/

universe u

/- Definition 29.48.1 (1): a finite locally free morphism is affine with finite locally free
pushforward structure sheaf. -/
@[stacks 02KA] #check
  (@AlgebraicGeometry.isFiniteLocallyFree_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.IsFiniteLocallyFree f ↔
        AlgebraicGeometry.IsAffineHom f ∧
          AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree
            (AlgebraicGeometry.Scheme.Hom.pushforwardStructureModule f))

/- Definition 29.48.1 (2): fixed-rank finite local freeness retains the morphism property and
adds rank `d` for the pushforward structure sheaf. -/
@[stacks 02KA] #check
  (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (d : ℕ),
      AlgebraicGeometry.IsFiniteLocallyFreeOfRank f d ↔
        AlgebraicGeometry.IsFiniteLocallyFree f ∧
          AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank d
            (AlgebraicGeometry.Scheme.Hom.pushforwardStructureModule f))
