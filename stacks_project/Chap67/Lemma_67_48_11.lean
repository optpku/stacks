/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Nagata

/-!
# Finiteness of relative normalizations over Nagata algebraic spaces
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.48.11: let `S` be a scheme, and let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `Y` is Nagata, `f` is quasi-separated of finite type,
and `X` is reduced, then the relative normalization `ν : Y' ⟶ Y` of `Y` in `X`,
namely `Hom.fromNormalization f : Hom.normalization f ⟶ Y`, is finite. -/
@[stacks 0BB0] #check
  (AlgebraicGeometry.AlgebraicSpace.IsFinite.fromNormalization_of_isNagata_of_finiteType :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [FiniteType f] [QuasiSeparated f] [IsNagata Y] [IsReduced X],
      IsFinite (Hom.fromNormalization f))

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.isFinite_fromNormalization_of_isNagata_of_finiteType :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [FiniteType f] [QuasiSeparated f] [IsNagata Y] [IsReduced X],
      IsFinite (Hom.fromNormalization f))
