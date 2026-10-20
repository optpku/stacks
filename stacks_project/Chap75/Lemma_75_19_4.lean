/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RightAdjoint.Boundedness
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Lemma 75.19.4: for a quasi-compact and quasi-separated algebraic space `X` over a
scheme `S`, there is a uniform integer `N` such that affine-étale hypercohomology of
`K` supported in `[a, b]` implies that the quasicoherent coreflection of `K` has
cohomology supported in `[a, b + N]`. -/
@[stacks 0CSS] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.rightAdjoint_bounds_of_affineEtaleHypercohomology :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X],
      ∃ N : ℤ, ∀ (K : ModuleDerived X) (a b : ℤ),
        (∀ {U : AlgebraicSpace S} (φ : U ⟶ X) [IsAffine U] [Etale φ],
          ∀ i : ℤ, i ∉ Set.Icc a b →
            IsZero (cohomologyAb U ((restrictFunctorDerived φ).obj K) i)) →
        ((inclusion X).rightAdjoint.obj K).obj.IsGE a ∧
          ((inclusion X).rightAdjoint.obj K).obj.IsLE (b + N))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
