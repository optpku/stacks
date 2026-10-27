/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Dimension.GenericRank
import StacksCheckRecall

@[expose] public section

open Module
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] [IsDomain R]

/- Definition (0H9U). The rank of an arbitrary module over a domain is the
cardinal dimension after extension to its fraction field. The canonical owner
is `Module.rank`; the formula below uses `FractionRing R` and the scalar-first
tensor product `FractionRing R ⊗[R] M`, canonically isomorphic to `M ⊗[R] FractionRing R`. -/
@[stacks 0H9U] #check
  (Module.rank_fractionRing_tensor : ∀ (R M : Type u) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M],
    Module.rank (FractionRing R) (FractionRing R ⊗[R] M) = Module.rank R M)
