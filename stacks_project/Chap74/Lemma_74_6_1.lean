/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteType.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

/- Lemma 74.6.1: a quasi-coherent module `ℱ` on an algebraic space `X` over a
scheme `S` is of finite type if its pullbacks along an fpqc covering family are
of finite type. -/
@[stacks 060U] #check (AlgebraicGeometry.AlgebraicSpace.Modules.IsFiniteType.of_fpqcCovering :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (family : ι → Over X) (hfamily : FpqcCovering family)
    (hpullback : ∀ i : ι, ((Modules.pullback (family i).hom).obj ℱ).IsFiniteType),
    ℱ.IsFiniteType)
