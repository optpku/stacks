module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing

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

/-- Lemma 66.22.4: let `S` be a scheme, let `X` be an algebraic space over `S`, let `x` be a
point of `|X|`, and let `d : WithBot ℕ∞`. The following are equivalent: the dimension of the
local ring of `X` at `x` is `d`; `ringKrullDim (etaleLocalRing X xbar) = d` for some geometric
point `xbar` lying over `x`; and `ringKrullDim (etaleLocalRing X xbar) = d` for every geometric
point `xbar` lying over `x`. -/
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
