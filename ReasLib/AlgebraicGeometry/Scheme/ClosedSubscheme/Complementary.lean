module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Union

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The scheme-theoretic closure in `X` of the open complement of a closed immersion. -/
noncomputable abbrev complementaryClosure {X Y : Scheme.{u}} (i : Y ⟶ X) : Scheme.{u} :=
  schemeTheoreticClosure (i.ker.openComplement)

/-- The canonical closed immersion of the complementary closure into the ambient scheme. -/
noncomputable abbrev complementaryClosureι {X Y : Scheme.{u}}
    (i : Y ⟶ X) : complementaryClosure i ⟶ X :=
  schemeTheoreticClosureι (i.ker.openComplement)

/-- The structure module on the scheme-theoretic intersection of a closed immersion and its
complementary closure, pushed forward to the ambient scheme. -/
noncomputable abbrev complementaryIntersectionStructureSheaf
    {X Y : Scheme.{u}} (i : Y ⟶ X) : X.Modules :=
  closedSubschemeStructureSheafOn
    (i.ker ⊔ (complementaryClosureι i).ker)

/-- The ideal sheaf of the intersection in the complementary closure. -/
noncomputable abbrev idealOnComplementaryClosure {X Y : Scheme.{u}} (i : Y ⟶ X) :
    (complementaryClosure i).IdealSheafData :=
  i.ker.comap (complementaryClosureι i)

/-- The ideal sheaf of the intersection in the original closed subscheme. -/
noncomputable abbrev idealOnClosedSubscheme {X Y : Scheme.{u}} (i : Y ⟶ X) :
    Y.IdealSheafData :=
  (complementaryClosureι i).ker.comap i

/-- The complementary closure inclusion is a canonical closed immersion. -/
instance complementaryClosure_isClosedImmersion {X Y : Scheme.{u}} (i : Y ⟶ X) :
    IsClosedImmersion (complementaryClosureι i) :=
  inferInstanceAs (IsClosedImmersion
    (schemeTheoreticClosureIdeal (i.ker.openComplement)).subschemeι)

/-- In a reduced ambient scheme, the defining ideals of a closed subscheme and its
complementary closure have zero intersection. -/
theorem complementaryClosure_ideal_inf_eq_bot {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] [IsReduced X] :
    i.ker ⊓ (complementaryClosureι i).ker = ⊥ := sorry

end AlgebraicGeometry.Scheme

end
