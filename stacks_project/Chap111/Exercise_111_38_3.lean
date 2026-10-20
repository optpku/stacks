/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Extension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Exercise 111.38.3: for a field `k` and a projective scheme `X` over `k`, every morphism
`φ : Spec (.of (RatFunc k)) ⟶ X` over `k` extends to a morphism
`ψ : Spec (.of (Polynomial k)) ⟶ X` over `k` along the inclusion `Polynomial k → RatFunc k`. -/
@[stacks 0DJ3] #check (AlgebraicGeometry.exists_hom_fromPolynomial :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Projective sX]
    (φ : Spec (.of (RatFunc k)) ⟶ X)
    (hφ : φ ≫ sX = Spec.map (CommRingCat.ofHom (algebraMap k (RatFunc k)))),
    ∃ ψ : Spec (.of (Polynomial k)) ⟶ X,
      ψ ≫ sX = Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) ∧
        Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (RatFunc k))) ≫ ψ = φ)

end AlgebraicGeometry
