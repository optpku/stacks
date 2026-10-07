module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Pullback

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry nonZeroDivisors

universe u

/- Lemma 38.43.2 (1): scalar extension constructs the affine chart on the pullback. -/
@[stacks 0F8T] #check
  (AlgebraicGeometry.Scheme.DivisorComplexChart.pullback :
    {X Y : Scheme.{u}} → (D : X.IdealSheafData) →
      [IsEffectiveCartierDivisor D.subschemeι] →
      (M : RingedSpace.ModuleDerived X.toRingedSpace) →
      RingedSpace.ModuleDerived.IsPerfect M → (h : Y ⟶ X) →
      D.pullbackDefined h →
      (C : AlgebraicGeometry.Scheme.DivisorComplexChart D M) →
      (V : Y.affineOpens) → V ≤ h ⁻¹ᵁ C.U →
      AlgebraicGeometry.Scheme.DivisorComplexChart (D.comap h)
        ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M))

/- Lemma 38.43.2 (2): the chart ideals commute with scalar extension. -/
@[stacks 0F8T] #check (AlgebraicGeometry.Scheme.DivisorComplexChart.ideal_pullback :
  {X Y : Scheme.{u}} → (D : X.IdealSheafData) →
    [IsEffectiveCartierDivisor D.subschemeι] →
    (M : RingedSpace.ModuleDerived X.toRingedSpace) →
    (hM : RingedSpace.ModuleDerived.IsPerfect M) → (h : Y ⟶ X) →
    (hpull : D.pullbackDefined h) →
    (C : AlgebraicGeometry.Scheme.DivisorComplexChart D M) →
    (V : Y.affineOpens) → (hV : V ≤ h ⁻¹ᵁ C.U) → (i : ℤ) →
    Ideal.map (h.appLE C.U V hV).hom (C.ideal i) =
      (C.pullback D M hM h hpull V hV).ideal i)

/- Lemma 38.43.2 (3): goodness is preserved by derived pullback. -/
@[stacks 0F8T] #check (AlgebraicGeometry.Scheme.IsGoodTriple.pullback :
  {X Y : Scheme.{u}} → (D : X.IdealSheafData) →
    [IsEffectiveCartierDivisor D.subschemeι] →
    (M : RingedSpace.ModuleDerived X.toRingedSpace) →
    RingedSpace.ModuleDerived.IsPerfect M → (h : Y ⟶ X) →
    D.pullbackDefined h → AlgebraicGeometry.Scheme.IsGoodTriple D M →
    AlgebraicGeometry.Scheme.IsGoodTriple (D.comap h)
      ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M))
