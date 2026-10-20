/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ReducedFiber.Separable
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 37.65.3 (Variant with separable extension): if `A` is a Nagata Dedekind domain,
`X` is flat and of finite type over `Spec(A)`, and the residue field at every generic point
of the generic fibre is separable over `FractionRing A`, then the finite extension used for
the normalized base change can be chosen separable while retaining smoothness in codimension
zero. -/
@[stacks 0BRR]
#check
  (AlgebraicGeometry.Scheme.Hom.exists_separable_normalizedBaseChange_smoothInCodimensionZero :
    ∀ {A : Type u} [CommRing A] [IsDedekindDomain A] [NagataRing A]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [Flat f]
      [AlgebraicGeometry.Scheme.Hom.FiniteType f],
      (let K := FractionRing A
       let gK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A) :=
         Spec.map (CommRingCat.ofHom (algebraMap A K))
       let X_K := pullback f gK
       ∀ η : X_K, η ∈ genericPoints X_K →
         AlgebraicGeometry.Scheme.Hom.ResidueField.IsSeparableOverSpec
           (pullback.snd f gK) η) →
      ∃ (L : Type u) (_ : Field L) (_ : Algebra A L)
          (_ : Algebra (FractionRing A) L)
          (_ : IsScalarTower A (FractionRing A) L)
          (_ : FiniteDimensional (FractionRing A) L)
          (_ : Algebra.IsSeparable (FractionRing A) L),
        let B := integralClosure A L
        -- Local instance justification (search instability): pin the canonical finite-extension Dedekind structure on the integral closure of `A` in the existentially chosen `L`, as required by normalization.
        letI : IsDedekindDomain B :=
          FractionRing.IntegralClosure.isDedekind_of_finite_extension
        let g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
          Spec.map (CommRingCat.ofHom (algebraMap A B))
        let X_B := pullback f g
        let Y := X_B.normalization
        let p : Y ⟶ Spec (CommRingCat.of B) :=
          X_B.normalizationTo ≫ pullback.snd f g
        p.smoothInCodimensionZero)
