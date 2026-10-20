module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.Contraction
public import ReasLib.AlgebraicGeometry.Scheme.Regular

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- The contraction API is owned by the mathematical ReasLib module. -/
/- AlgebraicGeometry.IsContraction is a proposition on a morphism and a closed center. -/
#check (AlgebraicGeometry.IsContraction :
  ∀ {X Y : Scheme.{u}} [IsNoetherian X] (E : X.IdealSheafData)
    [IsExceptionalCurveFirstKind E] (b : X ⟶ Y) (y : closedPoints Y), Prop)

/- The explicit constructor packages the six defining contraction conditions. -/
#check (AlgebraicGeometry.IsContraction.ofConditions :
  ∀ {X Y : Scheme.{u}} [IsNoetherian X] {E : X.IdealSheafData}
    [IsExceptionalCurveFirstKind E] {b : X ⟶ Y} {y : closedPoints Y},
    IsNoetherian Y → IsProper b →
      IsBlowup b (Scheme.IdealSheafData.vanishingIdeal
        (Scheme.PointClosure.closedSubset y.1)) →
      IsRegularLocalRing (Y.presheaf.stalk y.1) →
      ringKrullDim (Y.presheaf.stalk y.1) = 2 →
      E = (Scheme.IdealSheafData.vanishingIdeal
        (Scheme.PointClosure.closedSubset y.1)).comap b →
      AlgebraicGeometry.IsContraction E b y)

/- The support-level mapping property is part of the contraction API. -/
#check (AlgebraicGeometry.IsContraction.mapsToCenter :
  ∀ {X Y : Scheme.{u}} [IsNoetherian X] {E : X.IdealSheafData}
    [IsExceptionalCurveFirstKind E] {b : X ⟶ Y} {y : closedPoints Y},
    AlgebraicGeometry.IsContraction E b y →
      Set.MapsTo b E.support ({y.1} : Set Y))

/- The defining conditions admit a conjunction characterization. -/
#check (AlgebraicGeometry.isContraction_iff :
  ∀ {X Y : Scheme.{u}} [IsNoetherian X] (E : X.IdealSheafData)
    [IsExceptionalCurveFirstKind E] (b : X ⟶ Y) (y : closedPoints Y),
    AlgebraicGeometry.IsContraction E b y ↔
      IsNoetherian Y ∧ IsProper b ∧
        IsBlowup b (Scheme.IdealSheafData.vanishingIdeal
          (Scheme.PointClosure.closedSubset y.1)) ∧
        IsRegularLocalRing (Y.presheaf.stalk y.1) ∧
        ringKrullDim (Y.presheaf.stalk y.1) = 2 ∧
        E = (Scheme.IdealSheafData.vanishingIdeal
          (Scheme.PointClosure.closedSubset y.1)).comap b)

end AlgebraicGeometry
