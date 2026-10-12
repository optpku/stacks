/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived

/-!
# Derived sections on open subsets

This leaf owns the unbounded derived section functor `RΓ(U, -)` for an open subset of a ringed
space, its abelian-valued counterpart, open hypercohomology, and the derived restriction of
scalars induced by a morphism of ringed spaces.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/-- The cochain-level sections functor on `U`, followed by passage to the derived category. -/
abbrev moduleSectionsAtOpenToDerived
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    CochainComplex X.Modules ℤ ⥤ DerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  (moduleSectionsEvaluationFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

/-- The cochain-level sections functor on an open subset admits an unbounded total right derived
functor. -/
theorem moduleSectionsAtOpenToDerived_hasRightDerivedFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Functor.HasRightDerivedFunctor
      (moduleSectionsAtOpenToDerived X U)
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) := sorry

/-- The canonical right-derived-functor witness for cochain-level sections on an open subset. -/
instance moduleSectionsAtOpenToDerived_hasRightDerivedFunctor_instance
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Functor.HasRightDerivedFunctor
      (moduleSectionsAtOpenToDerived X U)
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) := sorry

/-- The total right derived functor `RΓ(U, -)` with values in modules over `Γ(U, 𝒪_X)`. -/
abbrev moduleDerivedSectionsAtOpen
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules] (U : Opens X.carrier) :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat (sectionsRingOnOpen X U)) :=
  (moduleSectionsAtOpenToDerived X U).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The canonical unit exhibiting `RΓ(U, -)` as the total right derived functor of cochain-level
sections on `U`. -/
noncomputable abbrev moduleSectionsAtOpenDerivedUnit
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    moduleSectionsAtOpenToDerived X U ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙
        moduleDerivedSectionsAtOpen X U :=
  (moduleSectionsAtOpenToDerived X U).totalRightDerivedUnit
    DerivedCategory.Q
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The chosen `RΓ(U, -)` carries the canonical right-derived-functor structure. -/
instance moduleSectionsAtOpenDerived_isRightDerivedFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleDerivedSectionsAtOpen X U).IsRightDerivedFunctor
      (moduleSectionsAtOpenDerivedUnit X U)
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) := sorry

/-- `RΓ(U, -)` after forgetting the `Γ(U, 𝒪_X)`-module structure of its values. -/
abbrev moduleDerivedSectionsAtOpenToAb
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules] (U : Opens X.carrier) :
    DerivedCategory X.Modules ⥤ DerivedCategory AddCommGrpCat.{u} :=
  moduleDerivedSectionsAtOpen X U ⋙
    (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).mapDerivedCategory

/-- The total right derived functor of ordinary abelian-group-valued sections on `U`. -/
abbrev moduleSectionsAsAbelianDerived
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules] (U : Opens X.carrier) :
    DerivedCategory X.Modules ⥤ DerivedCategory AddCommGrpCat.{u} :=
  Functor.RightDerived.Cochain.functor (moduleSectionsAsAbelianFunctor X U)

/-- Forgetting the section-module structure commutes canonically with derived sections on an open
subset. -/
theorem moduleDerivedSectionsAtOpenToAb_isomorphic_moduleSectionsAsAbelianDerived
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules] (U : Opens X.carrier) :
    IsIsomorphic
      (moduleDerivedSectionsAtOpenToAb X U)
      (moduleSectionsAsAbelianDerived X U) := sorry

/-- The open hypercohomology group `H^p(U, K)` of a derived `𝒪_X`-module. -/
abbrev moduleOpenHypercohomology
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [IsGrothendieckAbelian X.Modules]
    (K : DerivedCategory (RingedSpace.Modules X)) (p : ℤ) : AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).obj
    ((DerivedCategory.homologyFunctor (ModuleCat (sectionsRingOnOpen X U)) p).obj
      ((moduleDerivedSectionsAtOpen X U).obj K))

/-- Degree-`p` cohomology on an open subset, functorially valued in modules
over its section ring. -/
noncomputable abbrev moduleCohomologyAtOpenFunctor
    (X : RingedSpace.{u}) [HasInjectiveResolutions X.Modules]
    (U : Opens X.carrier) (p : ℕ) :
    X.Modules ⥤ ModuleCat (sectionsRingOnOpen X U) :=
  (moduleSectionsEvaluationFunctor X U).rightDerived p

/-- The degree-`p` cohomology of a module sheaf on an open subset, as a module over its section
ring. -/
abbrev moduleCohomologyAtOpen
    [HasInjectiveResolutions X.Modules]
    (U : Opens X.carrier) (ℱ : RingedSpace.Modules X) (p : ℕ) :
    ModuleCat (sectionsRingOnOpen X U) :=
  (moduleCohomologyAtOpenFunctor X U p).obj ℱ

/-- Restriction of scalars between section-module categories preserves finite limits. -/
instance moduleSectionsRestrictionFunctor_preservesFiniteLimits
    (f : X ⟶ Y) (V : Opens Y.carrier) :
    PreservesFiniteLimits (moduleSectionsRestrictionFunctor f V) := sorry

/-- Restriction of scalars between section-module categories preserves finite colimits. -/
instance moduleSectionsRestrictionFunctor_preservesFiniteColimits
    (f : X ⟶ Y) (V : Opens Y.carrier) :
    PreservesFiniteColimits (moduleSectionsRestrictionFunctor f V) := sorry

/-- The exact derived restriction-of-scalars functor induced by a morphism of ringed spaces over
an open subset. -/
abbrev moduleSectionsRestrictionDerived (f : X ⟶ Y) (V : Opens Y.carrier) :
    DerivedCategory (ModuleCat (sectionsRingOnOpen X (preimageOpen f V))) ⥤
      DerivedCategory (ModuleCat (sectionsRingOnOpen Y V)) :=
  (moduleSectionsRestrictionFunctor f V).mapDerivedCategory

end AlgebraicGeometry.RingedSpace


namespace RingedSpaceDerivedSectionsAtOpenToAb

/-- Notation for the abelian-valued derived sections functor on an open subset. -/
scoped notation3:max "RΓ[" U "]" =>
  AlgebraicGeometry.RingedSpace.moduleDerivedSectionsAtOpenToAb _ U

end RingedSpaceDerivedSectionsAtOpenToAb

namespace RingedSpaceOpenHypercohomology

/-- Notation for open hypercohomology. -/
scoped notation:max "H^" p:max "(" U ", " K ")" =>
  AlgebraicGeometry.RingedSpace.moduleOpenHypercohomology _ U K p

end RingedSpaceOpenHypercohomology
