/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.InclusionLocus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Exercise 111.46.3: two fibrewise non-dense effective Cartier divisors on a smooth
projective curve family over a finite-type base have a canonical closed inclusion locus,
whose closed points detect scheme-theoretic inclusion of the fibres. -/
@[stacks 0EGB] #check
  (AlgebraicGeometry.Curve.mem_inclusionIdeal_support_iff :
    ∀ {k : Type u} [Field k] (X T : SchemeOverField k)
      [IsAlgClosed k] [Curve X] [Smooth X.hom] [Scheme.Hom.FiniteType T.hom]
      (h_projective : ∃ n : ℕ, ∃ i : X.left ⟶ ProjectiveSpace.scheme k n,
        IsClosedImmersion i ∧ i ≫ ProjectiveSpace.toSpec k n = X.hom)
      (D₁ D₂ : (pullback X.hom T.hom).IdealSheafData)
      [IsEffectiveCartierDivisor D₁.subschemeι]
      [IsEffectiveCartierDivisor D₂.subschemeι]
      (hD₁ : Curve.avoidsGenericPointOnFibers X T D₁)
      (hD₂ : Curve.avoidsGenericPointOnFibers X T D₂)
      (t : T.left) (ht : t ∈ closedPoints T.left),
      t ∈ (D₁.inclusionIdeal D₂ (pullback.snd X.hom T.hom)).support ↔
        D₂.comap ((pullback.snd X.hom T.hom).fiberι t) ≤
          D₁.comap ((pullback.snd X.hom T.hom).fiberι t))
