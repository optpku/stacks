/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing

/-!
# Dimension of étale local rings

The dimension of the local ring of an algebraic space at a point equals the Krull dimension of
the étale-site stalk at some, equivalently any, geometric point over that point.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The Krull dimension of the étale-site stalk `etaleLocalRing X xbar` equals the dimension of
the local ring of `X` at the image point of `xbar`. -/
theorem ringKrullDim_etaleLocalRing_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    ringKrullDim (etaleLocalRing X xbar) = localRingDimAt xbar.image :=
  sorry

/-- For an algebraic space `X`, a point `x`, and `d : WithBot ℕ∞`, the following are equivalent:
the dimension of the local ring of `X` at `x` is `d`; the étale-site stalk at some geometric
point over `x` has Krull dimension `d`; and the étale-site stalk at every geometric point over
`x` has Krull dimension `d`. -/
@[stacks 04N9]
theorem etaleLocalRing_ringKrullDim_tfae {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (d : WithBot ℕ∞) :
    List.TFAE
      [localRingDimAt x = d,
        ∃ xbar : GeometricPoint X, xbar.liesOver x ∧ ringKrullDim (etaleLocalRing X xbar) = d,
        ∀ xbar : GeometricPoint X, xbar.liesOver x → ringKrullDim (etaleLocalRing X xbar) = d] :=
  sorry

/-- The dimension of the local ring of `X` at `x` is `d` if and only if the étale-site stalk
`etaleLocalRing X xbar` has Krull dimension `d` for some geometric point `xbar` lying over `x`. -/
theorem localRingDimAt_eq_iff_exists_etaleLocalRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (d : WithBot ℕ∞) :
    localRingDimAt x = d ↔
      ∃ xbar : GeometricPoint X, xbar.liesOver x ∧ ringKrullDim (etaleLocalRing X xbar) = d :=
  sorry

/-- The dimension of the local ring of `X` at `x` is `d` if and only if the étale-site stalk
`etaleLocalRing X xbar` has Krull dimension `d` for every geometric point `xbar` lying over `x`. -/
theorem localRingDimAt_eq_iff_forall_etaleLocalRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (d : WithBot ℕ∞) :
    localRingDimAt x = d ↔
      ∀ xbar : GeometricPoint X, xbar.liesOver x → ringKrullDim (etaleLocalRing X xbar) = d :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
