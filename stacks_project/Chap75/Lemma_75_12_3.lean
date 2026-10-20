/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Injective
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 75.12.3. Let `S` be a scheme. Let `f : X ⟶ Y` be a flat, quasi-compact,
and quasi-separated morphism of algebraic spaces over `S`. If `J` is an injective
object of `QCoh X`, then `f_* J` is an injective object of `QCoh Y`. -/
@[stacks 09TK] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.pushforward.injective_obj :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
      [AlgebraicGeometry.AlgebraicSpace.QuasiSeparated f]
      [AlgebraicGeometry.AlgebraicSpace.Flat f]
      (J : AlgebraicGeometry.AlgebraicSpace.QCoh X) (hJ : CategoryTheory.Injective J),
      CategoryTheory.Injective
        ((AlgebraicGeometry.AlgebraicSpace.QCoh.pushforward f).obj J))
