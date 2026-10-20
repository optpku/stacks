/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
public import ReasLib.Topology.Opens.Instances
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Derived global sections of modules on ringed spaces

This leaf adds the unbounded total right derived functor to the ordinary module-valued
global-sections API in `Module.GlobalSections`.
-/

@[expose] public section

open CategoryTheory ComplexShape Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

namespace Module.Derived.GlobalSections

/-- Global sections bundled as a left-exact functor. -/
@[stacks 05S9 "left-exact global sections"]
noncomputable abbrev leftExactFunctor (X : RingedSpace.{u}) :
    X.Modules ⥤ₗ ModuleCat (globalSectionsRing X) :=
  LeftExactFunctor.of (moduleGlobalSectionsFunctor X)

/-- The total right derived global-sections functor on `𝒪_X`-modules. -/
@[stacks 05S9 "total right-derived global sections"]
abbrev functor (X : RingedSpace.{u}) :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Functor.RightDerived.Homotopy.functor (moduleGlobalSectionsFunctor X)

/-- The canonical cochain-level unit for total right-derived global sections. -/
@[stacks 05S9 "unit for total right-derived global sections"]
noncomputable abbrev unit (X : RingedSpace.{u}) :
    (moduleGlobalSectionsFunctor X).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex (ModuleCat (globalSectionsRing X)) ℤ ⥤
          DerivedCategory (ModuleCat (globalSectionsRing X))) ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙ functor X :=
  Functor.RightDerived.Homotopy.cochainUnit (moduleGlobalSectionsFunctor X)

/-- The chosen global-sections functor satisfies the total right-derived universal property. -/
@[stacks 05S9 "total right-derived global sections"]
instance isRightDerived (X : RingedSpace.{u}) :
    (functor X).IsRightDerivedFunctor (unit X)
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) := sorry

/-- The homotopy-level global-sections functor is source-defined at every complex with
respect to quasi-isomorphisms. -/
instance everywhereDefined (X : RingedSpace.{u}) :
    Functor.RightDerived.EverywhereDefined
      (Functor.Homotopy.toDerived (moduleGlobalSectionsFunctor X))
      (HomotopyCategory.quasiIso X.Modules (up ℤ)) := sorry

/-- Derived global sections after forgetting the global-section module structure. -/
@[stacks 08C1 "abelian-valued derived global sections"]
abbrev toAbelian (X : RingedSpace.{u}) :
    DerivedCategory X.Modules ⥤ DerivedCategory AddCommGrpCat.{u} :=
  functor X ⋙
    (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory

/-- The cochain-level abelian-valued derived global-sections functor. -/
@[stacks 08C1 "cochain-level abelian-valued derived global sections"]
abbrev cochainToAbelian (X : RingedSpace.{u}) :
    CochainComplex X.Modules ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙ toAbelian X

/-- Ordinary global sections of a module sheaf, after forgetting scalars, are canonically the
global sections of its underlying additive sheaf. -/
@[stacks 08C1 "module global sections and underlying sheaf sections"]
noncomputable def additiveIso (X : RingedSpace.{u}) :
    (moduleGlobalSectionsFunctor X ⋙
      forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}) ≅
      SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
        Sheaf.Γ (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} := by
  -- Local instance justification (defeq pin): `ΓNatIsoSheafSections` is indexed by the chosen
  -- terminal-arrow family, and this canonical family is the top-open morphism on `Opens X`.
  letI : ∀ U : Opens X.carrier, Nonempty (U ⟶ (⊤ : Opens X.carrier)) := fun U ↦
    ⟨homOfLE le_top⟩
  change
    (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
      (sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).flip.obj
        (op (⊤ : Opens X.carrier))) ≅
      SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
        Sheaf.Γ (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}
  exact Functor.isoWhiskerLeft (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X))
    ((Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X.carrier)
      AddCommGrpCat.{u} (Preorder.isTerminalTop (Opens X.carrier))).symm)

/-- The underlying additive global-sections functor is additive. -/
@[stacks 08C1 "additivity of underlying global sections"]
instance additive (X : RingedSpace.{u}) :
    (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
      Sheaf.Γ (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).Additive :=
  Functor.additive_of_iso (additiveIso X)

/-- The underlying additive global-sections functor preserves zero morphisms. -/
@[stacks 08C1 "zero morphisms for underlying global sections"]
instance preservesZeroMorphisms (X : RingedSpace.{u}) :
    (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
      Sheaf.Γ (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- The additive global-sections comparison after applying the cochain-complex functor. -/
@[stacks 08C1 "complex-level underlying global-sections comparison"]
noncomputable def additiveComplexIso (X : RingedSpace.{u}) :
    ((moduleGlobalSectionsFunctor X ⋙
        forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℤ)) ≅
      (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
        Sheaf.Γ (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
  NatIso.mapHomologicalComplex (additiveIso X) (ComplexShape.up ℤ)

/-- The canonical cochain-level unit for abelian-valued derived global sections. -/
@[stacks 08C1 "abelian-valued derived global-sections unit"]
noncomputable def cochainToAbelianUnit (X : RingedSpace.{u}) :
    (((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
      DerivedCategory.Q ⋙
        (forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory) ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙
        toAbelian X :=
  Functor.whiskerRight (unit X)
      ((forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory) ≫
    (Functor.associator
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules)
      (functor X)
      ((forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategory)).hom

/-- The component of `cochainToAbelianUnit` after replacing the source by the localized additive
global-sections complex. -/
@[stacks 08C1 "component of the abelian-valued derived global-sections unit"]
noncomputable def cochainToAbelianUnitApp (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ) :
    DerivedCategory.Q.obj ((((moduleGlobalSectionsFunctor X ⋙
          forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) ⟶
      ((DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙
        toAbelian X).obj K :=
  ((forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapDerivedCategoryFactors.inv.app
      (((moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
    (cochainToAbelianUnit X).app K

/-- Degree-`n` cohomology after total right-derived global sections. -/
@[stacks 05S9 "cohomology after total right-derived global sections"]
abbrev cohomologyFunctor (X : RingedSpace.{u}) (n : ℤ) :
    DerivedCategory X.Modules ⥤ ModuleCat (globalSectionsRing X) :=
  Functor.RightDerived.Homotopy.cohomologyFunctor (moduleGlobalSectionsFunctor X) n

/-- Degree-`n` cohomology after localizing a cochain complex and applying total right-derived
global sections. -/
@[stacks 05S9 "cochain-level total right-derived global-sections cohomology"]
abbrev cochainCohomologyFunctor (X : RingedSpace.{u}) (n : ℤ) :
    CochainComplex X.Modules ℤ ⥤ ModuleCat (globalSectionsRing X) :=
  Functor.RightDerived.Homotopy.cochainCohomologyFunctor
    (moduleGlobalSectionsFunctor X) n

/-- The degree-`n` hypercohomology of a cochain complex of `𝒪_X`-modules. -/
@[stacks 05S9 "hypercohomology of a cochain complex"]
abbrev cochainCohomology (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ) (n : ℤ) : ModuleCat (globalSectionsRing X) :=
  Functor.RightDerived.Homotopy.cochainCohomology
    (moduleGlobalSectionsFunctor X) K n

/-- The map on hypercohomology induced by a cochain map of `𝒪_X`-modules. -/
@[stacks 05S9 "map on hypercohomology"]
abbrev cochainCohomologyMap (X : RingedSpace.{u})
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) (n : ℤ) :
    cochainCohomology X K n ⟶ cochainCohomology X L n :=
  Functor.RightDerived.Homotopy.cochainCohomologyMap
    (moduleGlobalSectionsFunctor X) f n

/-- Scoped notation for the derived global-sections functor `RΓ(X, -)` on a ringed space. -/
scoped[RingedSpaceDerivedGlobalSections] notation3:max "RΓ(" X ")" =>
  AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.functor X

end Module.Derived.GlobalSections

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.RingedSpace

/-- Total right-derived global sections on a ringed space. -/
@[stacks 05S9 "derived global sections"]
abbrev moduleDerivedGlobalSections (X : RingedSpace.{u}) :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Module.Derived.GlobalSections.functor X

/-- The degree-`p` cohomology functor of derived global sections. -/
@[stacks 0H3E "derived global-sections cohomology functor"]
abbrev moduleDerivedCohomologyFunctor (X : RingedSpace.{u}) (p : ℤ) :
    DerivedCategory X.Modules ⥤ ModuleCat (globalSectionsRing X) :=
  moduleDerivedGlobalSections X ⋙
    DerivedCategory.homologyFunctor (ModuleCat (globalSectionsRing X)) p

end AlgebraicGeometry.RingedSpace
