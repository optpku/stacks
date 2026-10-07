module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ReducedFiber.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Closure

/-!
# Separable normalized base changes with smooth generic points

This module provides a separable finite-extension construction whose normalized base change is
smooth at every generic point of every fibre.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- If `A` is a Nagata Dedekind domain, `X` is flat and of finite type over `Spec(A)`, and the
residue fields at the generic points of the generic fibre are separable over `FractionRing A`,
then the finite extension producing a normalized base change smooth at every generic point of
every fibre can be chosen separable. -/
theorem exists_separable_normalizedBaseChange_smoothInCodimensionZero
    {A : Type u} [CommRing A] [IsDedekindDomain A] [NagataRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [Flat f]
    [FiniteType f]
    (h_generic_sep :
      let K := FractionRing A
      let gK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A) :=
        Spec.map (CommRingCat.ofHom (algebraMap A K))
      let X_K := pullback f gK
      ∀ η : X_K, η ∈ genericPoints X_K →
        ResidueField.IsSeparableOverSpec (pullback.snd f gK) η) :
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
      p.smoothInCodimensionZero := sorry

end AlgebraicGeometry.Scheme.Hom
