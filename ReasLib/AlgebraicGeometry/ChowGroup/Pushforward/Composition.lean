module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward

/-!
# Composition of proper pushforwards on Chow groups

This file records functoriality of proper pushforward on relative Chow groups.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Proper pushforward on relative Chow groups is compatible with composition. -/
theorem map_comp
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y Z : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f.left] [IsProper g.left] (k : ℤ) :
    (map δ Y Z g k).comp (map δ X Y f k) =
      @map S inferInstance δ inferInstance X Z inferInstance inferInstance (f ≫ g)
        (Eq.mpr (congrArg IsProper (Over.comp_left X Y Z f g))
          (inferInstance : IsProper (f.left ≫ g.left))) k := sorry

end AlgebraicGeometry.ChowGroup
