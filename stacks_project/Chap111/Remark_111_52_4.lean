/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.KrullDimension.Chains
public import ReasLib.Topology.KrullDimension.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Dimension.IrreducibleComponents
public import ReasLib.RingTheory.KrullDimension.FiniteType.PrincipalQuotient
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u v

/- Remark 111.52.4 (1): the dimension of a scheme is the supremum of the lengths of chains
of irreducible closed subsets. The formula also applies to arbitrary topological spaces. -/
@[stacks 02AZ] #check (topologicalKrullDim_eq_iSup_chainLength :
    ∀ (X : Type u) [TopologicalSpace X],
      topologicalKrullDim X =
        ⨆ chain : LTSeries (TopologicalSpace.IrreducibleCloseds X),
          (chain.length : WithBot ℕ∞))

/- Remark 111.52.4 (2): the dimension of a finite-type scheme over a field is the maximum
of the dimensions of its affine opens. -/
@[stacks 02AZ] #check
  (AlgebraicGeometry.SchemeOverField.isGreatest_topologicalKrullDim_affineOpens :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X],
      IsGreatest
        {d : WithBot ℕ∞ |
          ∃ U : X.left.affineOpens, d = topologicalKrullDim (U : Set X.left)}
        (topologicalKrullDim X.left))

#check (AlgebraicGeometry.SchemeOverField.topologicalKrullDim_eq_iSup_affineOpens :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X],
      topologicalKrullDim X.left =
        ⨆ U : X.left.affineOpens, topologicalKrullDim (U : Set X.left))

/- Remark 111.52.4 (3): the dimension of a Noetherian scheme is the maximum of the dimensions
of its irreducible components. The source omits the necessary nonemptiness qualification:
an empty scheme has no irreducible component attaining a maximum. -/
@[stacks 02AZ] #check
  (AlgebraicGeometry.Scheme.isGreatest_topologicalKrullDim_irreducibleComponents :
    ∀ (X : Scheme.{u}) [IsNoetherian X] [Nonempty X],
      IsGreatest
        {d : WithBot ℕ∞ |
          ∃ Z : irreducibleComponents X, d = topologicalKrullDim (Z : Set X)}
        (topologicalKrullDim X))

#check (AlgebraicGeometry.Scheme.topologicalKrullDim_eq_iSup_irreducibleComponents :
    ∀ (X : Scheme.{u}) [IsNoetherian X],
      topologicalKrullDim X =
        ⨆ Z : irreducibleComponents X, topologicalKrullDim (Z : Set X))

#check (topologicalKrullDim_eq_iSup_irreducibleComponents :
    ∀ {X : Type u} [TopologicalSpace X] [NoetherianSpace X],
      topologicalKrullDim X =
        ⨆ Z : irreducibleComponents X, topologicalKrullDim (Z : Set X))

/- Remark 111.52.4 (4): the dimension of an affine scheme coincides with the Krull dimension
of its ring of global sections `Γ(X, ⊤)`. -/
@[stacks 02AZ] #check
  (AlgebraicGeometry.Scheme.topologicalKrullDim_eq_ringKrullDim_of_isAffine :
    ∀ (X : Scheme.{u}) [IsAffine X],
      topologicalKrullDim X = ringKrullDim Γ(X, ⊤))

#check (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim :
    ∀ (R : Type u) [CommSemiring R],
      topologicalKrullDim (PrimeSpectrum R) = ringKrullDim R)

/- Remark 111.52.4 (5): for a finite-type algebra domain over a field, a nonzero nonunit `x`
satisfies `ringKrullDim A = ringKrullDim (A ⧸ Ideal.span {x}) + 1`. The source omits the
necessary nonunit qualification: a unit gives the zero quotient of dimension `⊥`, and
`⊥ + 1 = ⊥` in `WithBot ℕ∞`. -/
@[stacks 02AZ] #check
  (Algebra.FiniteType.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim :
    ∀ {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
      [Algebra.FiniteType k A] {x : A},
      x ≠ 0 → ¬ IsUnit x → ringKrullDim A = ringKrullDim (A ⧸ Ideal.span {x}) + 1)
