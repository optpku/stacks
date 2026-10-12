/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Cohomology.RHomExt
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition

/-! The specified comparison between scalar-restricted sections and the
proper-pushforward presentation of cohomology over a field. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.Cohomology

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Ground-field scalar restriction of derived sections agrees with derived
sections of the direct image, through the specified pushforward comparison. -/
def sectionsPushforwardIso (p : X ⟶ Spec (CommRingCat.of k))
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    (ModuleCat.derivedRestrictionOfScalars p.globalSectionsMap).obj
        ((RingedSpace.moduleDerivedGlobalSections X.toRingedSpace).obj E) ≅
      (ModuleCat.derivedRestrictionOfScalars (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).obj
        ((RingedSpace.moduleDerivedGlobalSections (Spec (CommRingCat.of k)).toRingedSpace).obj
          ((RingedSpace.moduleDerivedPushforward p.toShHom).obj E)) :=
  ModuleCat.DerivedRestriction.compObjIsoOfEq
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom p.appTop.hom p.globalSectionsMap
      p.globalSectionsMap_eq_appTop
      ((RingedSpace.moduleDerivedGlobalSections X.toRingedSpace).obj E) ≪≫
    (ModuleCat.derivedRestrictionOfScalars
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).mapIso
        ((RingedSpace.Module.Derived.GlobalSections.pushforwardIso p.toShHom).app E)

/-- Degree conversion for the actual scalar-restricted global-sections functor. -/
def globalDegreeIso (p : X ⟶ Spec (CommRingCat.of k))
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (i : ℤ) :
    (globalCohomologyOverField p 0).obj (E⟦i⟧) ≅
      (globalCohomologyOverField p i).obj E :=
  let G := RingedSpace.moduleDerivedGlobalSections X.toRingedSpace ⋙
    ModuleCat.derivedRestrictionOfScalars p.globalSectionsMap
  -- Local instance justification (defeq pin): use the composed canonical derived sections shift for the comparison.
  letI := globalSectionsShift p
  (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).mapIso ((G.commShiftIso i).app E) ≪≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftIso i 0 i
      (add_zero i)).app (G.obj E)

/-- The actual sections model of proper cohomology is identified with the
existing shift-then-pushforward model, using only specified functor comparisons. -/
def properSectionsIso (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q]
    (L : Scheme.DerivedQCoh X) (i : ℤ) :
    (globalCohomologyOverField q i).obj L.obj ≅ cohomologyOverField q L i :=
  (globalDegreeIso q L.obj i).symm ≪≫
    (globalCohomologyOverField q 0).mapIso
      (((Scheme.DerivedQCoh.inclusion X).commShiftIso i).symm.app L) ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).mapIso
      (sectionsPushforwardIso q ((L⟦i⟧).obj))

end AlgebraicGeometry.Scheme.ModuleDerived.Cohomology
