module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.IdealSheaf

universe u

/- Good-triple modifications before and after pullback determine a unique comparison
morphism over the original scheme. -/
#check (AlgebraicGeometry.Scheme.IsGoodTripleModification.existsUniqueBaseChangeLift :
  {X X' Y Y' : Scheme.{u}} → (D : X.IdealSheafData) →
    [IsEffectiveCartierDivisor D.subschemeι] →
    (M : RingedSpace.ModuleDerived X.toRingedSpace) →
    (hM : RingedSpace.ModuleDerived.IsPerfect M) → (h : Y ⟶ X) →
    [IsEffectiveCartierDivisor (D.comap h).subschemeι] →
    (b : X' ⟶ X) → (c : Y' ⟶ Y) →
    [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b] →
    [AlgebraicGeometry.Scheme.IsGoodTripleModification (D.comap h)
      ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M) c] →
    ExistsUnique fun h' : Y' ⟶ X' ↦ h' ≫ b = c ≫ h)

/- Lemma 38.43.8 (1): the comparison morphism identifies `Y'` with the strict transform
of `Y` along `b`, compatibly with both projections. -/
@[stacks 0F8V] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.existsStrictTransformIso :
    {X X' Y Y' : Scheme.{u}} → (D : X.IdealSheafData) →
      [IsEffectiveCartierDivisor D.subschemeι] →
      (M : RingedSpace.ModuleDerived X.toRingedSpace) →
      (hM : RingedSpace.ModuleDerived.IsPerfect M) → (h : Y ⟶ X) →
      [IsEffectiveCartierDivisor (D.comap h).subschemeι] →
      (b : X' ⟶ X) → (c : Y' ⟶ Y) →
      [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b] →
      [AlgebraicGeometry.Scheme.IsGoodTripleModification (D.comap h)
        ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M) c] →
      (h' : Y' ⟶ X') → (h_fac : h' ≫ b = c ≫ h) →
      ∃ e : Y' ≅ strictTransform b (D.comap b) h,
        e.hom ≫ strictTransformFst b (D.comap b) h = c ∧
          e.hom ≫ strictTransformSnd b (D.comap b) h = h')

/- Lemma 38.43.8 (2): derived ideal-sheaf η after pullback along `c ≫ h` agrees,
up to isomorphism, with the pullback along the comparison morphism of the η-object on
the modification `X'`. -/
@[stacks 0F8V] #check (AlgebraicGeometry.Scheme.IsGoodTripleModification.etaPullback_isIsomorphic :
  {X X' Y Y' : Scheme.{u}} → (D : X.IdealSheafData) →
    [IsEffectiveCartierDivisor D.subschemeι] →
    (M : RingedSpace.ModuleDerived X.toRingedSpace) →
    (hM : RingedSpace.ModuleDerived.IsPerfect M) → (h : Y ⟶ X) →
    [IsEffectiveCartierDivisor (D.comap h).subschemeι] →
    (b : X' ⟶ X) → (c : Y' ⟶ Y) →
    [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b] →
    [AlgebraicGeometry.Scheme.IsGoodTripleModification (D.comap h)
      ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M) c] →
    (h' : Y' ⟶ X') → (h_fac : h' ≫ b = c ≫ h) →
    IsIsomorphic
      ((Eta.Derived.functor ((D.comap h).comap c).toSubobject).obj
        ((RingedSpace.modulePullbackDerived (c ≫ h).toLRSHom.toShHom).obj M))
      ((RingedSpace.modulePullbackDerived h'.toLRSHom.toShHom).obj
        ((Eta.Derived.functor (D.comap b).toSubobject).obj
          ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M))))

/- Lemma 38.43.8 (3): when the pulled-back triple on `Y` is already good, derived η
commutes up to isomorphism with pullback along its factorization through `b`. -/
@[stacks 0F8V] #check
  (AlgebraicGeometry.Scheme.IsGoodTripleModification.etaPullback_isIsomorphic_of_isGoodTriple :
    {X X' Y : Scheme.{u}} → (D : X.IdealSheafData) →
      [IsEffectiveCartierDivisor D.subschemeι] →
      (M : RingedSpace.ModuleDerived X.toRingedSpace) →
      (hM : RingedSpace.ModuleDerived.IsPerfect M) → (h : Y ⟶ X) →
      [IsEffectiveCartierDivisor (D.comap h).subschemeι] →
      (b : X' ⟶ X) →
      [AlgebraicGeometry.Scheme.IsGoodTripleModification D M b] →
      (h_good : AlgebraicGeometry.Scheme.IsGoodTriple (D.comap h)
        ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M)) →
      (k : Y ⟶ X') → (k_fac : k ≫ b = h) →
      IsIsomorphic
        ((Eta.Derived.functor (D.comap h).toSubobject).obj
          ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M))
        ((RingedSpace.modulePullbackDerived k.toLRSHom.toShHom).obj
          ((Eta.Derived.functor (D.comap b).toSubobject).obj
            ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M))))
