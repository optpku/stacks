/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.RingTheory.Localization.FractionRing.IntegralClosure

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Normalization

/-- The normalization of the pullback to the spectrum of an integral closure makes
the two induced composites to the original spectrum equal. -/
theorem integralClosurePullback_condition
    (A L : Type u) [CommRing A] [IsDedekindDomain A] [Field L]
    [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A)) [Flat f]
    [Scheme.Hom.FiniteType f] :
    let B := integralClosure A L
    -- Local instance justification (search instability): the finite-extension theorem supplies the canonical Dedekind structure needed for normalization prerequisites.
    letI : IsDedekindDomain B :=
      FractionRing.IntegralClosure.isDedekind_of_finite_extension
    let g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A B))
    let X_B := pullback f g
    X_B.normalizationTo ≫ (pullback.fst f g ≫ f) =
      X_B.normalizationTo ≫ (pullback.snd f g ≫ g) := sorry

end AlgebraicGeometry.Scheme.Normalization
