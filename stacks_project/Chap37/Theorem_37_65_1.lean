/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ReducedFiber.Normalization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Theorem 37.65.1: if `A` is a Nagata Dedekind domain and `X` is flat and of finite type
over `Spec(A)`, then after a finite extension of `FractionRing A`, the normalization of the
corresponding base change is smooth at every generic point of every fibre over the integral
closure of `A`. -/
@[stacks 09IL]
#check
  (AlgebraicGeometry.Scheme.Hom.exists_normalizedBaseChange_smoothInCodimensionZero :
    ∀ {A : Type u} [CommRing A] [IsDedekindDomain A] [NagataRing A]
        {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [Flat f] [FiniteType f],
      ∃ (L : Type u) (_ : Field L) (_ : Algebra A L)
          (_ : Algebra (FractionRing A) L)
          (_ : IsScalarTower A (FractionRing A) L)
          (_ : FiniteDimensional (FractionRing A) L),
        let B := integralClosure A L
        -- Local instance justification (search instability): the chosen extension may be inseparable, so the finite-extension theorem supplies the Dedekind structure needed for normalization without introducing a competing global instance.
        letI : IsDedekindDomain B :=
          FractionRing.IntegralClosure.isDedekind_of_finite_extension
        let g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
          Spec.map (CommRingCat.ofHom (algebraMap A B))
        let X_B := pullback f g
        let Y := X_B.normalization
        let p : Y ⟶ Spec (CommRingCat.of B) :=
          X_B.normalizationTo ≫ pullback.snd f g
        p.smoothInCodimensionZero)

end AlgebraicGeometry.Scheme.Hom
