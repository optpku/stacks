/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.OpenImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

variable (X : LocallyRingedSpace.{u}) (U : Opens X)

/- Definition 26.3.3: the open subspace attached to `U` is the canonical
restriction `X.restrict U.isOpenEmbedding`. -/
@[stacks 01HG] #check X.restrict U.isOpenEmbedding
#check X.ofRestrict U.isOpenEmbedding
