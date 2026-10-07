module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Modification.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Eta.Derived.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Blowup

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace.IdealSheaf

universe u

namespace AlgebraicGeometry.Scheme.IsGoodTripleModification

/-- Good-triple modifications before and after pullback determine a unique comparison
morphism over the original scheme. -/
theorem existsUniqueBaseChangeLift {X X' Y Y' : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (h : Y ⟶ X)
    [IsEffectiveCartierDivisor (D.comap h).subschemeι]
    (b : X' ⟶ X) (c : Y' ⟶ Y) [IsGoodTripleModification D M b]
    [IsGoodTripleModification (D.comap h)
      ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M) c] :
    ExistsUnique fun h' : Y' ⟶ X' ↦ h' ≫ b = c ≫ h := sorry

/-- A comparison morphism between good-triple modifications identifies the pulled-back
modification with the strict transform, compatibly with both projections. -/
@[stacks 0F8V]
theorem existsStrictTransformIso {X X' Y Y' : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (h : Y ⟶ X)
    [IsEffectiveCartierDivisor (D.comap h).subschemeι]
    (b : X' ⟶ X) (c : Y' ⟶ Y) [IsGoodTripleModification D M b]
    [IsGoodTripleModification (D.comap h)
      ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M) c]
    (h' : Y' ⟶ X') (h_fac : h' ≫ b = c ≫ h) :
    ∃ e : Y' ≅ strictTransform b (D.comap b) h,
      e.hom ≫ strictTransformFst b (D.comap b) h = c ∧
        e.hom ≫ strictTransformSnd b (D.comap b) h = h' := sorry

/-- Derived ideal-sheaf eta after pullback to a good-triple modification agrees up to
isomorphism with the pullback of the eta object on the original modification. -/
@[stacks 0F8V]
theorem etaPullback_isIsomorphic {X X' Y Y' : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (h : Y ⟶ X)
    [IsEffectiveCartierDivisor (D.comap h).subschemeι]
    (b : X' ⟶ X) (c : Y' ⟶ Y) [IsGoodTripleModification D M b]
    [IsGoodTripleModification (D.comap h)
      ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M) c]
    (h' : Y' ⟶ X') (h_fac : h' ≫ b = c ≫ h) :
    IsIsomorphic
      ((Eta.Derived.functor ((D.comap h).comap c).toSubobject).obj
        ((RingedSpace.modulePullbackDerived (c ≫ h).toLRSHom.toShHom).obj M))
      ((RingedSpace.modulePullbackDerived h'.toLRSHom.toShHom).obj
        ((Eta.Derived.functor (D.comap b).toSubobject).obj
          ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M))) := sorry

/-- For a good pulled-back triple, derived ideal-sheaf eta commutes up to isomorphism with
pullback along any factorization through its good-triple modification. -/
@[stacks 0F8V]
theorem etaPullback_isIsomorphic_of_isGoodTriple
    {X X' Y : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (h : Y ⟶ X)
    [IsEffectiveCartierDivisor (D.comap h).subschemeι]
    (b : X' ⟶ X) [IsGoodTripleModification D M b]
    (h_good : IsGoodTriple (D.comap h)
      ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M))
    (k : Y ⟶ X') (k_fac : k ≫ b = h) :
    IsIsomorphic
      ((Eta.Derived.functor (D.comap h).toSubobject).obj
        ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M))
      ((RingedSpace.modulePullbackDerived k.toLRSHom.toShHom).obj
        ((Eta.Derived.functor (D.comap b).toSubobject).obj
          ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M))) := sorry

end AlgebraicGeometry.Scheme.IsGoodTripleModification
