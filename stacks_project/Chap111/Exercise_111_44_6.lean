/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Kunneth

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Scheme.Modules
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Exercise 111.44.6: let `k` be a field, let `X` and `Y` be schemes over `k`, and let `ℱ`,
resp. `𝒢`, be quasi-coherent modules on `X`, resp. `Y`. If `X` and `Y` are quasi-compact and
quasi-separated, then for every `n` the cohomology of
`pr₁^*ℱ ⊗ pr₂^*𝒢` on `X ×[Spec (CommRingCat.of k)] Y` is canonically isomorphic to
`⊕_{a + b = n} H^a(X, ℱ) ⊗[k] H^b(Y, 𝒢)`. -/
@[stacks 0DB9] #check
  (AlgebraicGeometry.Scheme.Modules.cohomologyKunnethOverField :
    ∀ {k : Type u} [Field k]
      (X Y : Over (Spec (CommRingCat.of k)))
      [CompactSpace X.left.carrier] [CompactSpace Y.left.carrier]
      [QuasiSeparatedSpace X.left.carrier] [QuasiSeparatedSpace Y.left.carrier]
      (ℱ : X.left.Modules) [ℱ.IsQuasicoherent]
      (𝒢 : Y.left.Modules) [𝒢.IsQuasicoherent]
      (n : ℕ),
      IsIsomorphic
        (Scheme.Hom.cohomology
          (Limits.pullback.fst X.hom Y.hom ≫ X.hom)
          (externalTensorProduct X.hom Y.hom ℱ 𝒢) n)
        (∐ fun pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n} ↦
          Scheme.Hom.cohomology X.hom ℱ pq.1.1 ⊗
            Scheme.Hom.cohomology Y.hom 𝒢 pq.1.2))

end AlgebraicGeometry.Scheme.Modules
