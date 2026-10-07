module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.OpenRestriction

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

universe u

/- Compatibility check of the promoted open-restriction comparison of compactly
supported pushforwards. -/
#check (AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.restrictionComparisons_eq :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    {U X Y : Scheme.FiniteTypeSeparatedOver S}
    {i : U ⟶ X} [IsOpenImmersion i.hom.left] {f : X ⟶ Y}
    {C : AlgebraicGeometry.Scheme.Compactification.Of.UpperShriekCompChoice i f}
    (M : AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.RestrictionModel i f C)
    (composition :
      AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.RestrictionModel.CompositionModel M)
    (compactification :
      AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.RestrictionModel.FixedCompactificationModel M),
    composition.comparison = M.comparison ∧
      compactification.comparison = M.comparison)
