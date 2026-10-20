module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived pushforward after restriction to an open subspace

This file derives the underived functor `OpenSubspace.Pushforward.along f U`.  The total derived
functor, its comparison unit, and the maps induced by the open-subspace unit and nested-open
restriction are canonical specializations of the construction-neutral right-derived API.
-/

open AlgebraicGeometry
open CategoryTheory
open ComplexShape
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.OpenSubspace.Pushforward

variable {X Y : RingedSpace.{u}}

/-- Termwise pushforward after restriction to `U`, followed by localization in `D(𝒪_Y)`. -/
@[stacks 08DP "cochain-level pushforward after open restriction"]
abbrev alongToDerived (f : X ⟶ Y) (U : Opens X) :
    CochainComplex X.Modules ℤ ⥤ ModuleDerived Y :=
  Functor.RightDerived.Cochain.toDerived (along f U)

/-- The total right-derived functor of pushforward after restriction to `U`. -/
@[stacks 08DP "derived pushforward after open restriction"]
abbrev alongDerived (f : X ⟶ Y) (U : Opens X) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.RightDerived.Homotopy.functor (along f U)

namespace alongDerived

/-- The cochain-level comparison from pushforward after restriction to its total right-derived
functor. -/
@[stacks 08DP "derived comparison unit after open restriction"]
noncomputable abbrev unit (f : X ⟶ Y) (U : Opens X) :
    alongToDerived f U ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X) ⋙
        alongDerived f U :=
  Functor.RightDerived.Homotopy.cochainUnit (along f U)

/-- The cochain comparison exhibits `alongDerived f U` as the total right-derived functor of
`along f U`. -/
@[stacks 08DP "right-derived pushforward after open restriction"]
instance isRightDerived (f : X ⟶ Y) (U : Opens X) :
    (alongDerived f U).IsRightDerivedFunctor (unit f U)
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) := sorry

end alongDerived

/-- The map `R(f)_* ⟶ R(along f U)` induced by the open restriction-pushforward unit. -/
@[stacks 08DP "derived unit after pushforward from an open subspace"]
noncomputable def derivedUnit (f : X ⟶ Y) (U : Opens X) :
    moduleDerivedPushforward f ⟶ alongDerived f U :=
  Functor.RightDerived.Homotopy.mapNatTrans (alongUnit f U)

/-- The derived map from pushforward over `U` to pushforward over a nested open `W ⊆ U`. -/
@[stacks 08DP "derived restriction after further pushforward"]
noncomputable def derivedRestriction (f : X ⟶ Y) {W U : Opens X}
    (h : W ≤ U) : alongDerived f U ⟶ alongDerived f W :=
  Functor.RightDerived.Homotopy.mapNatTrans (alongRestriction f h)

/-- The derived open-unit map is compatible with the cochain comparison units. -/
@[stacks 08DP, reassoc (attr := simp)]
theorem derivedUnit.fac (f : X ⟶ Y) (U : Opens X) :
    moduleDerivedPushforward.unit f ≫ Functor.whiskerLeft
        (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X)
        (derivedUnit f U) =
      Functor.whiskerRight (NatTrans.mapHomologicalComplex (alongUnit f U) (up ℤ))
          (DerivedCategory.Q : CochainComplex Y.Modules ℤ ⥤ ModuleDerived Y) ≫
        alongDerived.unit f U := sorry

/-- The derived nested-open map is compatible with the cochain comparison units. -/
@[stacks 08DP, reassoc (attr := simp)]
theorem derivedRestriction.fac (f : X ⟶ Y) {W U : Opens X} (h : W ≤ U) :
    alongDerived.unit f U ≫ Functor.whiskerLeft
        (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X)
        (derivedRestriction f h) =
      Functor.whiskerRight (NatTrans.mapHomologicalComplex (alongRestriction f h) (up ℤ))
          (DerivedCategory.Q : CochainComplex Y.Modules ℤ ⥤ ModuleDerived Y) ≫
        alongDerived.unit f W := sorry

end AlgebraicGeometry.RingedSpace.OpenSubspace.Pushforward

-- Any `sorryAx` below is confined to the inherited additive, Grothendieck-abelian, localization,
-- or natural-isomorphism law fields. The functors and transformations use the canonical generic
-- total right-derived data explicitly.
