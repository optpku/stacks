/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.QuasiCompact
import StacksCheckRecall

/-!
# Quasi-compact formal algebraic spaces

A formal algebraic space is quasi-compact when the equivalent conditions of
Lemma 87.17.1 hold.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v

/- Definition 87.17.2: Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. We say `X` is quasi-compact if the equivalent conditions of
Lemma 87.17.1 are satisfied. -/
@[stacks 0AJA] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsQuasiCompact :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsFormalAlgebraicSpace X], Prop)
