/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GeometricLift
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u v

/- Lemma 59.29.5: an étale covering of an étale neighborhood of a geometric point
contains a member admitting a lift of that geometric point compatible with the covering map. -/
@[stacks 03PR] #check (AlgebraicGeometry.Scheme.exists_lift_of_smallEtaleCover :
  ∀ {S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ S) (U : S.Etale)
    (pointLift : Spec (.of K) ⟶ U.left) (hpointLift : pointLift ≫ U.hom = s)
    {I : Type v} (V : I → S.Etale) (φ : ∀ i, V i ⟶ U)
    (hcover : Sieve.ofArrows V φ ∈ S.smallEtaleTopology U),
    ∃ (i : I) (lift : Spec (.of K) ⟶ (V i).left),
      lift ≫ (V i).hom = s ∧ lift ≫ (φ i).left = pointLift)
