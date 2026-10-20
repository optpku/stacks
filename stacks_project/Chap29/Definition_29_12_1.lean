/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {ι : Type v}
variable (L : ι → X.Modules) [∀ i : ι, Invertible (L i)]

/- Definition 29.12.1: Let `X` be a scheme and let `L : ι → X.Modules` be a family of
invertible `𝒪_X`-modules. The family is ample if `X` is quasi-compact and, for every `x : X`,
there are `i : ι`, `n : ℕ` with `0 < n`, and a global section of
`RingedSpace.TensorPower.sheaf (L i) n` such that `x` lies in its nonvanishing open and that
open is affine. -/
@[stacks 0FXR] #check (AlgebraicGeometry.Scheme.Modules.AmpleFamily L : Prop)

#check (AlgebraicGeometry.Scheme.Modules.ampleFamily_iff L :
  AlgebraicGeometry.Scheme.Modules.AmpleFamily L ↔
    IsCompact (Set.univ : Set X) ∧
      ∀ x : X, ∃ i : ι, ∃ n : ℕ, 0 < n ∧
        ∃ s : Γ(RingedSpace.TensorPower.sheaf (L i) n, ⊤),
          AffineOpenNeighborhood x
            ((inferInstance : Invertible (L i)).nonvanishingOpen s))

end AlgebraicGeometry.Scheme.Modules
