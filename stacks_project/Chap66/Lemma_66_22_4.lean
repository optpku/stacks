/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.EtaleLocalRing
import StacksCheckRecall

/-!
# Dimension of étale local rings

The dimension of the local ring of an algebraic space at a point equals the Krull dimension of
the étale-site stalk at some, equivalently any, geometric point over that point.
-/

open AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 66.22.4: let `S` be a scheme, let `X` be an algebraic space over `S`, let `x` be a
point of `|X|`, and let `d : WithBot ℕ∞`. The following are equivalent: the dimension of the
local ring of `X` at `x` is `d`; `ringKrullDim (etaleLocalRing X xbar) = d` for some geometric
point `xbar` lying over `x`; and `ringKrullDim (etaleLocalRing X xbar) = d` for every geometric
point `xbar` lying over `x`. -/
@[stacks 04N9] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing_ringKrullDim_tfae :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) (d : WithBot ℕ∞),
    List.TFAE
      [localRingDimAt x = d,
        ∃ xbar : GeometricPoint X, xbar.liesOver x ∧ ringKrullDim (etaleLocalRing X xbar) = d,
        ∀ xbar : GeometricPoint X, xbar.liesOver x → ringKrullDim (etaleLocalRing X xbar) = d])

#check (AlgebraicGeometry.AlgebraicSpace.ringKrullDim_etaleLocalRing_eq :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X),
    ringKrullDim (etaleLocalRing X xbar) = localRingDimAt xbar.image)

#check (AlgebraicGeometry.AlgebraicSpace.localRingDimAt_eq_iff_exists_etaleLocalRing :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) (d : WithBot ℕ∞),
    localRingDimAt x = d ↔
      ∃ xbar : GeometricPoint X, xbar.liesOver x ∧ ringKrullDim (etaleLocalRing X xbar) = d)

#check (AlgebraicGeometry.AlgebraicSpace.localRingDimAt_eq_iff_forall_etaleLocalRing :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) (d : WithBot ℕ∞),
    localRingDimAt x = d ↔
      ∀ xbar : GeometricPoint X, xbar.liesOver x → ringKrullDim (etaleLocalRing X xbar) = d)
