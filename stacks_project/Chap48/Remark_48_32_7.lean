/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.OpenRestriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

universe u

/- Remark 48.32.7: in Situation 48.16.1, for an open immersion `i : U ⟶ X` and
`f : X ⟶ Y`, the restriction transformation `Rg_! (K|_U) ⟶ Rf_! K`, natural in
`K`, obtained from represented Hom agrees both with the construction through
`Rf_! ∘ Ri_!` and with the construction using any fixed compactification. -/
@[stacks 0G56]
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
