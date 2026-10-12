/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.FiberCriterion
import StacksCheckRecall

/-!
# Lemma 31.18.9

Fiber criteria for relative effective Cartier divisors.

@stack 062Y
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 31.18.9 (1): a Cartier divisor in one fiber extends locally to a relative effective
Cartier divisor containing the given closed subscheme and having the same fiber. -/
@[stacks 062Y]
#check
  (AlgebraicGeometry.IsRelativeEffectiveCartierDivisor.exists_open_le_fiber_eq_of_isEffectiveCartierDivisor_near :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData)
      (x : Z.subscheme) [AlgebraicGeometry.Flat f]
      [AlgebraicGeometry.LocallyOfFinitePresentation f],
      (∃ W : (AlgebraicGeometry.Scheme.Hom.fiber f (f (Z.subschemeι x))).Opens,
          AlgebraicGeometry.Scheme.Hom.asFiber f (Z.subschemeι x) ∈
              (W : Set (AlgebraicGeometry.Scheme.Hom.fiber f (f (Z.subschemeι x)))) ∧
            AlgebraicGeometry.IsEffectiveCartierDivisor
              ((Z.comap (AlgebraicGeometry.Scheme.Hom.fiberι f (f (Z.subschemeι x)))).comap
                W.ι).subschemeι) →
        ∃ U : X.Opens,
          ∃ _ : Z.subschemeι x ∈ (U : Set X),
            ∃ D : U.toScheme.IdealSheafData,
              ∃ _ : AlgebraicGeometry.IsRelativeEffectiveCartierDivisor (U.ι ≫ f) D,
                ∃ _ : D ≤ Z.comap U.ι,
                  (Z.comap U.ι).comap
                      (AlgebraicGeometry.Scheme.Hom.fiberι (U.ι ≫ f) (f (Z.subschemeι x))) =
                    D.comap
                      (AlgebraicGeometry.Scheme.Hom.fiberι (U.ι ≫ f) (f (Z.subschemeι x))))

/- Lemma 31.18.9 (2): finite presentation and flatness of the closed subscheme at the point
allow the local relative effective Cartier divisor to equal the closed subscheme. -/
@[stacks 062Y]
#check
  (AlgebraicGeometry.IsRelativeEffectiveCartierDivisor.exists_open_eq_of_finitePresentation_flatAt :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData)
      (x : Z.subscheme) [AlgebraicGeometry.Flat f]
      [AlgebraicGeometry.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation Z.subschemeι],
      AlgebraicGeometry.Scheme.Hom.flatAt (Z.subschemeι ≫ f) x →
        (∃ W : (AlgebraicGeometry.Scheme.Hom.fiber f (f (Z.subschemeι x))).Opens,
            AlgebraicGeometry.Scheme.Hom.asFiber f (Z.subschemeι x) ∈
                (W : Set (AlgebraicGeometry.Scheme.Hom.fiber f (f (Z.subschemeι x)))) ∧
              AlgebraicGeometry.IsEffectiveCartierDivisor
                ((Z.comap
                  (AlgebraicGeometry.Scheme.Hom.fiberι f (f (Z.subschemeι x)))).comap W.ι).subschemeι) →
          ∃ U : X.Opens,
            ∃ _ : Z.subschemeι x ∈ (U : Set X),
              ∃ D : U.toScheme.IdealSheafData,
                ∃ _ : AlgebraicGeometry.IsRelativeEffectiveCartierDivisor (U.ι ≫ f) D,
                  Z.comap U.ι = D)

/- Lemma 31.18.9 (3): if the closed subscheme is locally principal near the point, the local
relative effective Cartier divisor can equal it. -/
@[stacks 062Y]
#check
  (AlgebraicGeometry.IsRelativeEffectiveCartierDivisor.exists_open_eq_of_locallyPrincipal_near :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData)
      (x : Z.subscheme) [AlgebraicGeometry.Flat f]
      [AlgebraicGeometry.LocallyOfFinitePresentation f],
      (∃ V : X.Opens,
          ∃ _ : Z.subschemeι x ∈ (V : Set X),
            AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme (Z.comap V.ι).subschemeι) →
        (∃ W : (AlgebraicGeometry.Scheme.Hom.fiber f (f (Z.subschemeι x))).Opens,
            AlgebraicGeometry.Scheme.Hom.asFiber f (Z.subschemeι x) ∈
                (W : Set (AlgebraicGeometry.Scheme.Hom.fiber f (f (Z.subschemeι x)))) ∧
              AlgebraicGeometry.IsEffectiveCartierDivisor
                ((Z.comap
                  (AlgebraicGeometry.Scheme.Hom.fiberι f (f (Z.subschemeι x)))).comap W.ι).subschemeι) →
          ∃ U : X.Opens,
            ∃ _ : Z.subschemeι x ∈ (U : Set X),
              ∃ D : U.toScheme.IdealSheafData,
                ∃ _ : AlgebraicGeometry.IsRelativeEffectiveCartierDivisor (U.ι ≫ f) D,
                  Z.comap U.ι = D)

/- Lemma 31.18.9 (4): a flat locally finitely presented closed subscheme whose fibers are
effective Cartier divisors is a relative effective Cartier divisor. -/
@[stacks 062Y]
#check
  (AlgebraicGeometry.IsRelativeEffectiveCartierDivisor.of_flat_locallyOfFinitePresentation_fibers :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData)
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.LocallyOfFinitePresentation (Z.subschemeι ≫ f)]
      [AlgebraicGeometry.Flat (Z.subschemeι ≫ f)],
      (∀ s : S,
          AlgebraicGeometry.IsEffectiveCartierDivisor
            (Z.comap (AlgebraicGeometry.Scheme.Hom.fiberι f s)).subschemeι) →
        AlgebraicGeometry.IsRelativeEffectiveCartierDivisor f Z)

/- Lemma 31.18.9 (5): a locally principal closed subscheme whose fibers are effective Cartier
divisors is a relative effective Cartier divisor. -/
@[stacks 062Y]
#check
  (AlgebraicGeometry.IsRelativeEffectiveCartierDivisor.of_locallyPrincipal_fibers :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData)
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme Z.subschemeι],
      (∀ s : S,
          AlgebraicGeometry.IsEffectiveCartierDivisor
            (Z.comap (AlgebraicGeometry.Scheme.Hom.fiberι f s)).subschemeι) →
        AlgebraicGeometry.IsRelativeEffectiveCartierDivisor f Z)
