/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative.Smooth
import StacksCheckRecall

/-!
# Lemma 108.9.5

If `f : X ⟶ B` is flat, proper, and of finite presentation, the structure-sheaf
maps `O_T ⟶ f_{T,*} O_{X_T}` are isomorphisms, and `f` has relative dimension at
most `1`, then the structure morphism of the Picard functor over `B` is smooth.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.9.5: if `f : X ⟶ B` is flat, proper, and of finite presentation,
the maps `O_T ⟶ f_{T,*} O_{X_T}` are isomorphisms for every scheme `T` over `B`,
and `f` has relative dimension at most `1`, then the relative Picard functor
is smooth over `B`. -/
@[stacks 0DPK] #check (AlgebraicGeometry.AlgebraicSpace.RelativePicard.isSmoothOver :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
    [Flat f] → [FinitePresentation f] → [Proper f] →
    [Hom.IsIsoBaseChangeStructurePushforward f] → [RelativeDimensionLE f 1] →
    IsSmoothOver (picardFunctor f).obj)
