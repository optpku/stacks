module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Open
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Restriction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived sections over global scalars

For an open `U ⊆ X`, this module views sections on `U` as modules over the global section ring
`Γ(X, 𝒪_X)`.  The ordinary section functor and its total right derived functor are the canonical
owners; the restriction maps and Mayer--Vietoris maps are thin natural-transformation bridges.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
  TopologicalSpace AlgebraicGeometry
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal

open AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The restriction-of-scalars functor from sections on `U` to global scalars. -/
@[stacks 01BH "restriction of section scalars"]
abbrev restrictionToGlobal (X : RingedSpace.{u}) (U : Opens X.carrier) :
    ModuleCat (sectionsRingOnOpen X U) ⥤ ModuleCat (globalSectionsRing X) :=
  ModuleCat.restrictScalars (globalSectionsToOpen (RingHom.id (globalSectionsRing X)) U)

/-- Sections on `U`, regarded as modules over `Γ(X, 𝒪_X)`. -/
@[stacks 01BH "sections over global scalars"]
abbrev functor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    X.Modules ⥤ ModuleCat (globalSectionsRing X) :=
  moduleSectionsEvaluationFunctor X U ⋙ restrictionToGlobal X U

/-- Restriction of scalars along the section-ring map is additive. -/
instance restrictionToGlobal_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (restrictionToGlobal X U).Additive := sorry

/-- The section functor over global scalars is additive. -/
instance functor_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (functor X U).Additive := sorry

/-- The section functor over global scalars preserves zero morphisms. -/
instance functor_preservesZeroMorphisms (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (functor X U).PreservesZeroMorphisms := sorry

/-- The cochain-level section functor over global scalars, followed by localization. -/
abbrev toDerived (X : RingedSpace.{u}) (U : Opens X.carrier) :
    CochainComplex X.Modules ℤ ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Functor.RightDerived.Cochain.toDerived (functor X U)

/-- The cochain-level section functor over global scalars has a total right derived functor. -/
instance toDerived_hasRightDerivedFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) [IsGrothendieckAbelian X.Modules] :
    (toDerived X U).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) := sorry

/-- The total right derived sections over global scalars. -/
@[stacks 05S9 "derived sections over global scalars"]
abbrev derived (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]
    (U : Opens X.carrier) :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Functor.RightDerived.Cochain.functor (functor X U)

/-- The canonical unit for derived sections over global scalars. -/
@[stacks 05S9 "derived sections unit over global scalars"]
noncomputable abbrev unit (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]
    (U : Opens X.carrier) :
    toDerived X U ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙
        derived X U :=
  Functor.RightDerived.Cochain.unit (functor X U)

/-- The derived sections over global scalars satisfy the right-derived universal property. -/
instance isRightDerived (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]
    (U : Opens X.carrier) :
    (derived X U).IsRightDerivedFunctor (unit X U)
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) := sorry

/-- The cochain-level global-sections functor, viewed at the terminal open. -/
abbrev globalToDerived (X : RingedSpace.{u}) :
  CochainComplex X.Modules ℤ ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Functor.RightDerived.Cochain.toDerived (moduleGlobalSectionsFunctor X)

/-- The cochain-level global-sections functor has the canonical right-derived witness. -/
instance globalToDerived_hasRightDerivedFunctor
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules] :
    (globalToDerived X).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) := sorry

/-- The total right derived global-sections functor used as the source of restriction maps. -/
@[stacks 05S9 "derived global sections source"]
abbrev globalDerived (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules] :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Module.Derived.GlobalSections.functor X

/-- The canonical unit for the derived global-sections source. -/
noncomputable abbrev globalUnit (X : RingedSpace.{u})
    [IsGrothendieckAbelian X.Modules] :
    globalToDerived X ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙
        globalDerived X :=
  Module.Derived.GlobalSections.unit X

/-- Restriction of module sections from `X` to `U`, after changing scalars to `Γ(X, 𝒪_X)`. -/
@[stacks 01BH "sections restriction to an open"]
noncomputable def restriction (X : RingedSpace.{u}) (U : Opens X.carrier) :
    moduleGlobalSectionsFunctor X ⟶ functor X U where
  app M := M.val.map (topOpenRestriction (X := X) (op U))
  naturality := sorry

/-- The induced natural transformation on cochain complexes. -/
abbrev restrictionOnComplexes (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleGlobalSectionsFunctor X).mapHomologicalComplex (up ℤ) ⟶
      (functor X U).mapHomologicalComplex (up ℤ) :=
  NatTrans.mapHomologicalComplex (restriction X U) (up ℤ)

/-- The derived restriction map from global sections to sections on `U`. -/
@[stacks 01BH "derived restriction to an open"]
noncomputable def derivedRestriction
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules] (U : Opens X.carrier) :
    globalDerived X ⟶ derived X U :=
  Functor.rightDerivedNatTrans
    (globalDerived X) (derived X U) (globalUnit X) (unit X U)
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (Functor.whiskerRight (restrictionOnComplexes X U) DerivedCategory.Q)

/-- The ring map on sections induced by an inclusion `U ≤ V`. -/
abbrev restrictionRingHom {U V : Opens X.carrier} (hUV : U ≤ V) :
    sectionsRingOnOpen X V →+* sectionsRingOnOpen X U :=
  (X.presheaf.map (homOfLE hUV).op).hom

/-- Restriction of global scalars to an open is compatible with restriction from a larger open. -/
theorem globalMap_comp_restrictionRingHom {U V : Opens X.carrier} (hUV : U ≤ V) :
    (restrictionRingHom (X := X) hUV).comp
        (globalSectionsToOpen (RingHom.id (globalSectionsRing X)) V) =
      globalSectionsToOpen (RingHom.id (globalSectionsRing X)) U := sorry

/-- The underived restriction natural transformation for nested opens. -/
noncomputable def restrictionOfLE {U V : Opens X.carrier} (hUV : U ≤ V) :
    functor X V ⟶ functor X U where
  app M :=
    (restrictionToGlobal X V).map (M.val.map (homOfLE hUV).op) ≫
      (ModuleCat.restrictScalarsComp'
        (globalSectionsToOpen (RingHom.id (globalSectionsRing X)) V)
        (restrictionRingHom (X := X) hUV)
        (globalSectionsToOpen (RingHom.id (globalSectionsRing X)) U)
        (globalMap_comp_restrictionRingHom (X := X) hUV).symm).inv.app (M.val.obj (op U))
  naturality := sorry

/-- The derived restriction natural transformation for nested opens. -/
noncomputable def derivedRestrictionOfLE
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]
    {U V : Opens X.carrier} (hUV : U ≤ V) :
    derived X V ⟶ derived X U :=
  Functor.rightDerivedNatTrans
    (derived X V) (derived X U) (unit X V) (unit X U)
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (restrictionOfLE hUV) (up ℤ))
      DerivedCategory.Q)

/-- The component of the nested derived restriction at a derived object. -/
abbrev derivedRestrictionOfLEApp
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]
    {U V : Opens X.carrier} (hUV : U ≤ V) (K : DerivedCategory X.Modules) :
    (derived X V).obj K ⟶ (derived X U).obj K :=
  (derivedRestrictionOfLE X hUV).app K

/-- The global-to-open derived restriction at a derived object. -/
abbrev derivedRestrictionApp
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]
    (U : Opens X.carrier) (K : DerivedCategory X.Modules) :
    (globalDerived X).obj K ⟶ (derived X U).obj K :=
  (derivedRestriction X U).app K

/-- The Mayer--Vietoris map from global derived sections to the biproduct of two open sections. -/
abbrev mayerVietorisToBiprod
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]
    (U V : Opens X.carrier) :
    globalDerived X ⟶ derived X U ⊞ derived X V :=
  biprod.lift (derivedRestriction X U) (derivedRestriction X V)

/-- The overlap-difference map for derived sections over global scalars. -/
abbrev mayerVietorisDifference
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]
    (U V : Opens X.carrier) :
    derived X U ⊞ derived X V ⟶ derived X (U ⊓ V) :=
  biprod.desc
    (derivedRestrictionOfLE X (show U ⊓ V ≤ U from inf_le_left))
    (-(derivedRestrictionOfLE X (show U ⊓ V ≤ V from inf_le_right)))

/-- The derived-sections Mayer--Vietoris triangle over global scalars. -/
@[stacks 08BX "derived sections Mayer--Vietoris triangle"]
theorem mayerVietorisTriangle
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) :
    ∃ δ : derived X (U ⊓ V) ⟶
        globalDerived X ⋙ shiftFunctor (DerivedCategory (ModuleCat (globalSectionsRing X)))
          (1 : ℤ),
      ∀ E : DerivedCategory X.Modules,
        Triangle.mk
            ((mayerVietorisToBiprod X U V).app E)
            ((mayerVietorisDifference X U V).app E)
            (δ.app E) ∈
          distTriang (DerivedCategory (ModuleCat (globalSectionsRing X))) := sorry

end AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal

namespace AlgebraicGeometry.RingedSpace

/-! Compatibility names for the former Chapter 20 surface.  The canonical owners live in
`Module.Derived.Sections.OverGlobal`; these abbreviations keep old downstream statements
source-compatible without creating a second implementation. -/

/-- Legacy name for `Module.Derived.Sections.OverGlobal.restrictionToGlobal`. -/
abbrev moduleSectionsRestrictionToGlobalFunctor (X : RingedSpace.{u})
    (U : Opens X.carrier) :
    ModuleCat (sectionsRingOnOpen X U) ⥤ ModuleCat (globalSectionsRing X) :=
  Module.Derived.Sections.OverGlobal.restrictionToGlobal X U

/-- Legacy name for `Module.Derived.Sections.OverGlobal.functor`. -/
abbrev moduleSectionsOverGlobalFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    X.Modules ⥤ ModuleCat (globalSectionsRing X) :=
  Module.Derived.Sections.OverGlobal.functor X U

/-- Legacy name for the cochain-level over-global sections functor. -/
abbrev moduleSectionsOverGlobalToDerived (X : RingedSpace.{u}) (U : Opens X.carrier) :
    CochainComplex X.Modules ℤ ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Module.Derived.Sections.OverGlobal.toDerived X U

/-- Legacy name for `Module.Derived.Sections.OverGlobal.derived`. -/
abbrev moduleDerivedSectionsOverGlobal (X : RingedSpace.{u})
    [IsGrothendieckAbelian X.Modules] (U : Opens X.carrier) :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Module.Derived.Sections.OverGlobal.derived X U

/-- Legacy name for the canonical derived-sections unit. -/
noncomputable abbrev moduleDerivedSectionsOverGlobalUnit (X : RingedSpace.{u})
    [IsGrothendieckAbelian X.Modules] (U : Opens X.carrier) :
    moduleSectionsOverGlobalToDerived X U ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙
        moduleDerivedSectionsOverGlobal X U :=
  Module.Derived.Sections.OverGlobal.unit X U

/-- Legacy name for the cochain-level global-sections functor. -/
abbrev moduleGlobalSectionsToDerived (X : RingedSpace.{u}) :
    CochainComplex X.Modules ℤ ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Module.Derived.Sections.OverGlobal.globalToDerived X

/-- Legacy name for the global-to-open restriction transformation. -/
noncomputable abbrev moduleSectionsOverGlobalRestrictionNatTrans
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    moduleGlobalSectionsFunctor X ⟶ moduleSectionsOverGlobalFunctor X U :=
  Module.Derived.Sections.OverGlobal.restriction X U

/-- Legacy name for the induced cochain-level restriction transformation. -/
abbrev moduleSectionsOverGlobalRestrictionNatTransOnComplexes
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (moduleSectionsOverGlobalFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Module.Derived.Sections.OverGlobal.restrictionOnComplexes X U

/-- Legacy name for the derived global-to-open restriction transformation. -/
noncomputable abbrev moduleDerivedSectionsOverGlobalRestrictionNatTrans
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules] (U : Opens X.carrier) :
    (Module.Derived.GlobalSections.functor X) ⟶ moduleDerivedSectionsOverGlobal X U :=
  Module.Derived.Sections.OverGlobal.derivedRestriction X U

/-- Legacy name for restriction between nested opens before deriving. -/
noncomputable abbrev moduleSectionsOverGlobalRestrictionNatTransOfLE
    {X : RingedSpace.{u}} {U V : Opens X.carrier} (hUV : U ≤ V) :
    moduleSectionsOverGlobalFunctor X V ⟶ moduleSectionsOverGlobalFunctor X U :=
  Module.Derived.Sections.OverGlobal.restrictionOfLE hUV

/-- Legacy name for restriction between nested opens after deriving. -/
noncomputable abbrev moduleDerivedSectionsOverGlobalRestrictionNatTransOfLE
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]
    {U V : Opens X.carrier} (hUV : U ≤ V) :
    moduleDerivedSectionsOverGlobal X V ⟶ moduleDerivedSectionsOverGlobal X U :=
  Module.Derived.Sections.OverGlobal.derivedRestrictionOfLE X hUV

/-- Legacy objectwise nested-open restriction. -/
abbrev moduleDerivedSectionsOverGlobalRestrictionOfLE
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]
    {U V : Opens X.carrier} (hUV : U ≤ V) (K : DerivedCategory X.Modules) :
    (moduleDerivedSectionsOverGlobal X V).obj K ⟶
      (moduleDerivedSectionsOverGlobal X U).obj K :=
  Module.Derived.Sections.OverGlobal.derivedRestrictionOfLEApp X hUV K

/-- Legacy objectwise global-to-open restriction. -/
abbrev moduleDerivedSectionsOverGlobalRestriction
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]
    (U : Opens X.carrier) (K : DerivedCategory X.Modules) :
    (Module.Derived.GlobalSections.functor X).obj K ⟶
      (moduleDerivedSectionsOverGlobal X U).obj K :=
  Module.Derived.Sections.OverGlobal.derivedRestrictionApp X U K

/-- Legacy Mayer--Vietoris map into the open-section biproduct. -/
abbrev moduleDerivedSectionsOverGlobalMayerVietorisToBiprod
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]
    (U V : Opens X.carrier) :
    Module.Derived.GlobalSections.functor X ⟶
      moduleDerivedSectionsOverGlobal X U ⊞ moduleDerivedSectionsOverGlobal X V :=
  Module.Derived.Sections.OverGlobal.mayerVietorisToBiprod X U V

/-- Legacy Mayer--Vietoris overlap-difference map. -/
abbrev moduleDerivedSectionsOverGlobalMayerVietorisDifference
    (X : RingedSpace.{u}) [IsGrothendieckAbelian X.Modules]
    (U V : Opens X.carrier) :
    moduleDerivedSectionsOverGlobal X U ⊞ moduleDerivedSectionsOverGlobal X V ⟶
      moduleDerivedSectionsOverGlobal X (U ⊓ V) :=
  Module.Derived.Sections.OverGlobal.mayerVietorisDifference X U V

end AlgebraicGeometry.RingedSpace
