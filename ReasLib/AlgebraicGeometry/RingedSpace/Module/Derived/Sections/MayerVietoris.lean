/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.Algebra.Homology.HomologicalComplex.Composition
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Nested-open restriction and Mayer--Vietoris hypercohomology

This leaf owns restriction of derived sections along `W ≤ U` in a fixed ringed space.  The
restriction-of-scalars functor is the data owner; the derived natural transformation, its
homology map, and the Mayer--Vietoris maps are named separately so later chapters can reuse them
without reconstructing scalar-change instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace AlgebraicGeometry
open ComplexShape

noncomputable section

universe u

universe vC uC vD uD vE uE

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Sections

variable {X : RingedSpace.{u}}

/-- Restriction of section scalars along an inclusion `W ≤ U`. -/
@[stacks 08BX "nested-open section restriction"]
abbrev restrictionFunctor {W U : Opens X.carrier} (h : W ≤ U) :
    ModuleCat.{u} (sectionsRingOnOpen X W) ⥤ ModuleCat.{u} (sectionsRingOnOpen X U) :=
  ModuleCat.restrictScalars (X.presheaf.map (homOfLE h).op).hom

/-- Evaluation at an open is additive in the nested-open restriction API. -/
@[stacks 08BX "open section evaluation additivity"]
instance evaluation_additive (W : Opens X.carrier) :
    (SheafOfModules.evaluation X.ringCatSheaf (op W)).Additive := sorry

/-- Restriction of scalars is additive in the nested-open restriction API. -/
@[stacks 08BX "nested-open restriction additivity"]
instance restrictionFunctor_additive {W U : Opens X.carrier} (h : W ≤ U) :
    (restrictionFunctor h).Additive := sorry

/-- Restriction of section scalars is exact. -/
@[stacks 08BX "nested-open restriction exactness"]
instance restrictionFunctor_preservesFiniteLimits {W U : Opens X.carrier} (h : W ≤ U) :
    PreservesFiniteLimits (restrictionFunctor h) := sorry

/-- Restriction of section scalars preserves finite colimits. -/
@[stacks 08BX "nested-open restriction finite colimits"]
instance restrictionFunctor_preservesFiniteColimits {W U : Opens X.carrier} (h : W ≤ U) :
    PreservesFiniteColimits (restrictionFunctor h) := sorry

/-- The underived section functor on `W`, followed by restriction of scalars to `Γ(U, 𝒪_X)`. -/
@[stacks 08BX "nested-open section restriction composite"]
abbrev restrictionComp {W U : Opens X.carrier} (h : W ≤ U) :
    X.Modules ⥤ ModuleCat.{u} (sectionsRingOnOpen X U) :=
  SheafOfModules.evaluation X.ringCatSheaf (op W) ⋙ restrictionFunctor h

/-- The nested-open section composite is additive. -/
@[stacks 08BX "nested-open section composite additivity"]
instance restrictionComp_additive {W U : Opens X.carrier} (h : W ≤ U) :
    (restrictionComp h).Additive := sorry

/-- The nested-open section composite preserves zero morphisms. -/
@[stacks 08BX "nested-open section composite zero morphisms"]
instance restrictionComp_preservesZeroMorphisms {W U : Opens X.carrier} (h : W ≤ U) :
    (restrictionComp h).PreservesZeroMorphisms := sorry

/-- The exact derived restriction functor on section-module derived categories. -/
@[stacks 08BX "nested-open derived restriction"]
abbrev restrictionDerived {W U : Opens X.carrier} (h : W ≤ U) :
    DerivedCategory (ModuleCat.{u} (sectionsRingOnOpen X W)) ⥤
      DerivedCategory (ModuleCat.{u} (sectionsRingOnOpen X U)) :=
  (restrictionFunctor h).mapDerivedCategory

/-- The underived restriction map of section modules, viewed as a natural transformation. -/
@[stacks 08BX "nested-open section restriction map"]
noncomputable def restrictionNatTrans {W U : Opens X.carrier} (h : W ≤ U) :
    SheafOfModules.evaluation X.ringCatSheaf (op U) ⟶
      restrictionComp h where
  app ℱ := ℱ.val.map (homOfLE h).op
  naturality := sorry

/-- The restriction map on cochain complexes. -/
@[stacks 08BX "nested-open restriction on complexes"]
noncomputable def restrictionOnComplexes {W U : Opens X.carrier} (h : W ≤ U) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).mapHomologicalComplex (up ℤ) ⟶
      (restrictionComp h).mapHomologicalComplex (up ℤ) where
  app K :=
    { f := fun i ↦ (restrictionNatTrans h).app (K.X i)
      comm' := sorry }
  naturality := sorry

/-- The canonical comparison between the cochain restriction and the derived restriction. -/
@[stacks 08BX "nested-open restriction comparison"]
noncomputable def restrictionIso {W U : Opens X.carrier} (h : W ≤ U) :
      (restrictionComp h).mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q ≅
      (moduleSectionsAtOpenToDerived X W ⋙ restrictionDerived h) :=
  let evaluation := SheafOfModules.evaluation X.ringCatSheaf (op W)
  let restrict : ModuleCat.{u} (sectionsRingOnOpen X W) ⥤
      ModuleCat.{u} (sectionsRingOnOpen X U) := restrictionFunctor h
  let evalW := evaluation.mapHomologicalComplex (up ℤ)
  let ecomp :
      (SheafOfModules.evaluation X.ringCatSheaf (op W) ⋙
        restrict) ≅ restrictionComp h :=
    Iso.refl _
  Functor.isoWhiskerRight
      (CategoryTheory.Functor.MapHomologicalComplex.compIsoOf
        evaluation restrict (restrictionComp h)
        (evaluation_additive W) (restrictionFunctor_additive h) (restrictionComp_additive h)
        ecomp (up ℤ)).symm
      DerivedCategory.Q ≪≫
    Functor.associator evalW (restrict.mapHomologicalComplex (up ℤ)) DerivedCategory.Q ≪≫
    Functor.isoWhiskerLeft evalW restrict.mapDerivedCategoryFactors.symm ≪≫
    (Functor.associator evalW DerivedCategory.Q restrict.mapDerivedCategory).symm

/-- The unit used to identify derived restriction with a right-derived functor. -/
@[stacks 08BX "nested-open restriction derived unit"]
noncomputable abbrev restrictionUnit {W U : Opens X.carrier} (h : W ≤ U) :
    (moduleSectionsAtOpenToDerived X W ⋙ restrictionDerived (X := X) h) ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙
        (moduleDerivedSectionsAtOpen X W ⋙ restrictionDerived (X := X) h) :=
  Functor.whiskerRight (moduleSectionsAtOpenDerivedUnit X W)
      (restrictionDerived (X := X) h) ≫
    (Functor.associator (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules)
      (moduleDerivedSectionsAtOpen X W) (restrictionDerived (X := X) h)).hom

/-- The canonical derived restriction map on derived sections. -/
@[stacks 08BX "nested-open derived section map"]
noncomputable def restriction {W U : Opens X.carrier} (h : W ≤ U) :
    moduleDerivedSectionsAtOpen X U ⟶
      moduleDerivedSectionsAtOpen X W ⋙ restrictionDerived (X := X) h :=
  Functor.rightDerivedNatTrans
    (moduleDerivedSectionsAtOpen X U)
    (moduleDerivedSectionsAtOpen X W ⋙ restrictionDerived h)
    (moduleSectionsAtOpenDerivedUnit X U)
    (restrictionUnit h)
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    ((Functor.whiskerRight (restrictionOnComplexes h) DerivedCategory.Q) ≫
      (restrictionIso h).hom)

/-- The component of derived restriction at an object. -/
@[stacks 08BX "nested-open derived section map component"]
abbrev restrictionApp {W U : Opens X.carrier} (h : W ≤ U)
    (E : DerivedCategory X.Modules) :
    (moduleDerivedSectionsAtOpen X U).obj E ⟶
      (restrictionDerived h).obj ((moduleDerivedSectionsAtOpen X W).obj E) :=
  (restriction h).app E

/-- Restriction on degree-`n` open hypercohomology. -/
@[stacks 08BX "nested-open hypercohomology restriction"]
noncomputable def hyperRestriction {W U : Opens X.carrier} (h : W ≤ U)
    (E : DerivedCategory X.Modules) (n : ℤ) :
    moduleOpenHypercohomology X U E n ⟶ moduleOpenHypercohomology X W E n :=
  let F := restrictionFunctor (X := X) h
  let Fd := restrictionDerived (X := X) h
  let e := exactFunctor_homology_iso_mapDerivedCategory F
      ((moduleDerivedSectionsAtOpen X W).obj E) n
  let targetIso :
      (forget₂ (ModuleCat.{u} (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (sectionsRingOnOpen X U)) n).obj
          (Fd.obj ((moduleDerivedSectionsAtOpen X W).obj E))) ≅
        moduleOpenHypercohomology X W E n :=
    (forget₂ (ModuleCat.{u} (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).mapIso e.symm
  (forget₂ (ModuleCat.{u} (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (sectionsRingOnOpen X U)) n).map
        (restrictionApp h E)) ≫ targetIso.hom

namespace MayerVietoris

/-- The first Mayer--Vietoris map on open hypercohomology. -/
@[stacks 08BX "Mayer--Vietoris restriction map"]
abbrev toBiprod (U V : Opens X.carrier) (E : DerivedCategory X.Modules) (n : ℤ) :
    moduleOpenHypercohomology X (⊤ : Opens X.carrier) E n ⟶
      moduleOpenHypercohomology X U E n ⊞ moduleOpenHypercohomology X V E n :=
  biprod.lift (hyperRestriction (show U ≤ (⊤ : Opens X.carrier) from le_top) E n)
    (hyperRestriction (show V ≤ (⊤ : Opens X.carrier) from le_top) E n)

/-- The overlap-difference map on open hypercohomology. -/
@[stacks 08BX "Mayer--Vietoris overlap difference"]
abbrev difference (U V : Opens X.carrier) (E : DerivedCategory X.Modules) (n : ℤ) :
    moduleOpenHypercohomology X U E n ⊞ moduleOpenHypercohomology X V E n ⟶
      moduleOpenHypercohomology X (U ⊓ V) E n :=
  biprod.desc (hyperRestriction (show U ⊓ V ≤ U from inf_le_left) E n)
    (-hyperRestriction (show U ⊓ V ≤ V from inf_le_right) E n)

/-- The five-term Mayer--Vietoris exact segment on open hypercohomology. -/
@[stacks 08BX "Mayer--Vietoris hypercohomology exact segment"]
theorem exact (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (E : DerivedCategory X.Modules) (n : ℤ) :
    ∃ δ : moduleOpenHypercohomology X (U ⊓ V) E n ⟶
        moduleOpenHypercohomology X (⊤ : Opens X.carrier) E (n + 1),
      (ComposableArrows.mk₅ (toBiprod U V E n) (difference U V E n) δ
        (toBiprod U V E (n + 1)) (difference U V E (n + 1))).Exact := sorry

end MayerVietoris

end AlgebraicGeometry.RingedSpace.ModuleDerived.Sections

end
