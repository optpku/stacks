/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph.Stability
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/- Lemma 34.8.8 (1): if `T' ⟶ T` is an isomorphism, then the singleton family
`{T' ⟶ T}` is a ph covering of `T`. -/
@[stacks 0DBI] #check
  (AlgebraicGeometry.phCoveringSingletonOfIsIso :
    ∀ {T T' : Scheme.{u}} (f : T' ⟶ T) [IsIso f],
      PhCovering (fun _ : PUnit ↦ T') (fun _ : PUnit ↦ f))

/- Lemma 34.8.8 (2): if `{T_i ⟶ T}` is a ph covering and each `{T_{ij} ⟶ T_i}`
is a ph covering, then the composite family `{T_{ij} ⟶ T}` is a ph covering. -/
@[stacks 0DBI] #check
  (AlgebraicGeometry.phCoveringComp :
    ∀ {T : Scheme.{u}} {I : Type v}
      (X : I → Scheme.{u}) (π : ∀ i, X i ⟶ T) [PhCovering X π]
      (J : I → Type w) (Y : ∀ i, J i → Scheme.{u})
      (ρ : ∀ i, ∀ j : J i, Y i j ⟶ X i) [∀ i, PhCovering (Y i) (ρ i)],
        PhCovering (fun p : Sigma J ↦ Y p.1 p.2)
          (fun p : Sigma J ↦ ρ p.1 p.2 ≫ π p.1))

/- Lemma 34.8.8 (3): if `{T_i ⟶ T}` is a ph covering and `T' ⟶ T` is any morphism,
then the base-change family `{T_i ×_T T' ⟶ T'}` is a ph covering. -/
@[stacks 0DBI] #check
  (AlgebraicGeometry.phCoveringPullback :
    ∀ {T T' : Scheme.{u}} {I : Type v}
      (X : I → Scheme.{u}) (π : ∀ i, X i ⟶ T) [PhCovering X π] (f : T' ⟶ T),
        PhCovering (fun i : I ↦ pullback (π i) f)
          (fun i : I ↦ pullback.snd (π i) f))

end AlgebraicGeometry
