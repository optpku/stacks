/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

open CategoryTheory

universe u v

@[expose] public section

namespace AlgebraicGeometry.Scheme

/-- An indexed covering of an étale scheme over `S` contains a member to which a given
algebraically closed field-valued point lifts, compatibly with both the structure morphism
and the covering morphism. -/
theorem exists_lift_of_smallEtaleCover
    {S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ S) (U : S.Etale)
    (pointLift : Spec (.of K) ⟶ U.left) (hpointLift : pointLift ≫ U.hom = s)
    {I : Type v} (V : I → S.Etale) (φ : ∀ i, V i ⟶ U)
    (hcover : Sieve.ofArrows V φ ∈ S.smallEtaleTopology U) :
    ∃ (i : I) (lift : Spec (.of K) ⟶ (V i).left),
      lift ≫ (V i).hom = s ∧ lift ≫ (φ i).left = pointLift := sorry

end AlgebraicGeometry.Scheme
