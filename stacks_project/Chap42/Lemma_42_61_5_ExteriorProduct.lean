module

public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- The compatibility module exposes the canonical associativity theorem with its complete
field-specific type. -/
#check (AlgebraicGeometry.ChowGroup.Total.exteriorProduct_assoc :
  {k : Type u} → [Field k] →
    {X Y Z : AlgebraicGeometry.SchemeOverField k} →
    [AlgebraicGeometry.LocallyOfFiniteType X.hom] →
    [AlgebraicGeometry.LocallyOfFiniteType Y.hom] →
    [AlgebraicGeometry.LocallyOfFiniteType Z.hom] →
    (alpha : AlgebraicGeometry.ChowGroup.Total (fun _ ↦ 0) X) →
    (beta : AlgebraicGeometry.ChowGroup.Total (fun _ ↦ 0) Y) →
    (gamma : AlgebraicGeometry.ChowGroup.Total (fun _ ↦ 0) Z) →
    AlgebraicGeometry.ChowGroup.Total.map (fun _ ↦ 0)
        (Limits.prod.associator X Y Z).hom
        (AlgebraicGeometry.ChowGroup.Total.exteriorProduct (X ⨯ Y) Z
          (AlgebraicGeometry.ChowGroup.Total.exteriorProduct X Y alpha beta) gamma) =
      AlgebraicGeometry.ChowGroup.Total.exteriorProduct X (Y ⨯ Z) alpha
        (AlgebraicGeometry.ChowGroup.Total.exteriorProduct Y Z beta gamma))
