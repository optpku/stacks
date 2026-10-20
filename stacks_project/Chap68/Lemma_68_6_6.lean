/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable.Etale
import StacksCheckRecall

/-!
# Étale ascent of decent and reasonable algebraic spaces

If `f : X ⟶ Y` is an étale morphism of algebraic spaces over a scheme `S`, then
decency and reasonableness of `Y` pass to `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 68.6.6 (1): Let `S` be a scheme. If `f : X ⟶ Y` is an étale morphism of
algebraic spaces over `S` and `Y` is decent, then `X` is decent. -/
@[stacks 0ABU] #check (AlgebraicGeometry.AlgebraicSpace.IsDecent.of_etale :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.Etale f] [AlgebraicGeometry.AlgebraicSpace.IsDecent Y],
    AlgebraicGeometry.AlgebraicSpace.IsDecent X)

/- Lemma 68.6.6 (2): Let `S` be a scheme. If `f : X ⟶ Y` is an étale morphism of
algebraic spaces over `S` and `Y` is reasonable, then `X` is reasonable. -/
@[stacks 0ABU] #check (AlgebraicGeometry.AlgebraicSpace.IsReasonable.of_etale :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.Etale f] [AlgebraicGeometry.AlgebraicSpace.IsReasonable Y],
    AlgebraicGeometry.AlgebraicSpace.IsReasonable X)
