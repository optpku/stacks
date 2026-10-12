/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived global sections on a closed subset

For a ringed space `X` and a bundled closed subset `Z`, this file separates two constructions:

* `ClosedSubset.GlobalSections` derives global sections of modules living on `Z`, with values in
  modules over `Γ(X, 𝒪_X)`;
* `ClosedSubset.GlobalSectionsWithSupport` derives global sections of ambient modules supported
  on `Z`.

The comparison morphisms are built from the universal property of right derived functors. The
underived and derived forget-support morphisms are owned here rather than reconstructed from a
particular derived adjunction presentation.
-/

@[expose] public section

open CategoryTheory ComplexShape TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset

variable (X : RingedSpace.{u}) (Z : Closeds X)

namespace GlobalSections

/-- Global sections of a module on `Z`, regarded as a module over `Γ(X, 𝒪_X)`. -/
@[stacks 0G70 "closed-subset module global sections"]
abbrev functor :
    RingedSpace.ClosedSubset.Modules X Z ⥤ ModuleCat (globalSectionsRing X) :=
  RingedSpace.ClosedSubset.pushforward X Z ⋙ moduleGlobalSectionsFunctor X

/-- The cochain-level closed-subset global-sections functor followed by localization. -/
@[stacks 0G70 "closed-subset global-sections cochain localization"]
abbrev toDerived :
    CochainComplex (RingedSpace.ClosedSubset.Modules X Z) ℤ ⥤
      DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Functor.Derived.Cochain.toDerived (functor X Z)

/-- Total right-derived global sections of modules living on `Z`. -/
@[stacks 0G70 "derived closed-subset module global sections"]
abbrev derived :
    ModuleDerived X Z ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Functor.RightDerived.Cochain.functor (functor X Z)

/-- The canonical unit for derived global sections of modules living on `Z`. -/
@[stacks 0G70 "closed-subset derived global-sections unit"]
abbrev unit :
    toDerived X Z ⟶
      (DerivedCategory.Q :
        CochainComplex (RingedSpace.ClosedSubset.Modules X Z) ℤ ⥤ ModuleDerived X Z) ⋙
        derived X Z :=
  Functor.RightDerived.Cochain.unit (functor X Z)

/-- The global-sections unit, presented with direct image as the first cochain functor. -/
@[stacks 0G70 "closed-subset global-sections comparison unit"]
abbrev comparisonUnit :
    (RingedSpace.ClosedSubset.pushforward X Z).mapHomologicalComplex (up ℤ) ⋙
        Functor.RightDerived.Cochain.toDerived (moduleGlobalSectionsFunctor X) ⟶
      (DerivedCategory.Q :
        CochainComplex (RingedSpace.ClosedSubset.Modules X Z) ℤ ⥤ ModuleDerived X Z) ⋙
        derived X Z :=
  unit X Z

/-- Derived global sections on a closed subset satisfy the right-derived universal property. -/
@[stacks 0G70 "closed-subset derived global-sections universal property"]
noncomputable instance isRightDerived :
    (derived X Z).IsRightDerivedFunctor (unit X Z)
      (HomologicalComplex.quasiIso
        (RingedSpace.ClosedSubset.Modules X Z) (up ℤ)) := sorry

/-- The direct-image presentation of the global-sections unit satisfies the same right-derived
universal property. -/
@[stacks 0G70 "closed-subset global-sections comparison-unit universal property"]
noncomputable instance comparisonUnitIsRightDerived :
    (derived X Z).IsRightDerivedFunctor (comparisonUnit X Z)
      (HomologicalComplex.quasiIso
        (RingedSpace.ClosedSubset.Modules X Z) (up ℤ)) := sorry

/-- Compute closed-subset global sections by derived direct image followed by ambient derived
global sections. -/
@[stacks 0G70 "closed-subset ambient derived global-sections model"]
abbrev ambientDerived :
    ModuleDerived X Z ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Pushforward.derived X Z ⋙ Module.Derived.GlobalSections.functor X

section AmbientComparison

variable [comparisonDerived :
  (derived X Z).IsRightDerivedFunctor (comparisonUnit X Z)
    (HomologicalComplex.quasiIso
      (RingedSpace.ClosedSubset.Modules X Z) (up ℤ))]

/-- The canonical comparison from derived global sections on `Z` to derived direct image
followed by ambient derived global sections. -/
@[stacks 0G70 "closed-subset global-sections composition comparison"]
noncomputable def ambientComparison : derived X Z ⟶ ambientDerived X Z :=
  Functor.RightDerived.Composition.comparisonOfModels
    (F := (RingedSpace.ClosedSubset.pushforward X Z).mapHomologicalComplex (up ℤ))
    (G := Functor.Derived.Cochain.toDerived (moduleGlobalSectionsFunctor X))
    (HomologicalComplex.quasiIso (RingedSpace.ClosedSubset.Modules X Z) (up ℤ))
    (Pushforward.factors X Z).inv (Module.Derived.GlobalSections.unit X)
    (comparisonUnit X Z)

/-- The cochain-level unit whose universal-property lift is `ambientComparison`. -/
@[stacks 0G70 "closed-subset ambient global-sections comparison unit"]
noncomputable abbrev ambientUnit :
    (RingedSpace.ClosedSubset.pushforward X Z).mapHomologicalComplex (up ℤ) ⋙
        Functor.Derived.Cochain.toDerived (moduleGlobalSectionsFunctor X) ⟶
      (DerivedCategory.Q :
        CochainComplex (RingedSpace.ClosedSubset.Modules X Z) ℤ ⥤ ModuleDerived X Z) ⋙
        ambientDerived X Z :=
  Functor.RightDerived.Composition.iteratedUnit
    (Pushforward.factors X Z).inv (Module.Derived.GlobalSections.unit X)

/-- The ambient comparison is characterized by its cochain-level factorization. -/
@[reassoc (attr := simp), stacks 0G70 "closed-subset ambient comparison factorization"]
theorem ambientComparison_fac :
    comparisonUnit X Z ≫ Functor.whiskerLeft
        (DerivedCategory.Q :
          CochainComplex (RingedSpace.ClosedSubset.Modules X Z) ℤ ⥤ ModuleDerived X Z)
        (ambientComparison X Z) =
      ambientUnit X Z := sorry

/-- The closed-subset global-sections composition comparison is invertible. -/
@[stacks 0G70 "closed-subset global-sections composition comparison isomorphism"]
noncomputable instance ambientComparisonIsIso : IsIso (ambientComparison X Z) := sorry

variable [comparisonIsoWitness : IsIso (ambientComparison X Z)]

/-- The named inverse of the closed-subset ambient global-sections comparison. -/
@[stacks 0G70 "inverse closed-subset ambient global-sections comparison"]
noncomputable def ambientComparisonInv : ambientDerived X Z ⟶ derived X Z :=
  CategoryTheory.inv (ambientComparison X Z)

/-- The ambient comparison followed by its named inverse is the identity. -/
@[stacks 0G70 "closed-subset ambient comparison inverse law"]
theorem ambientComparison_comp_inv :
    ambientComparison X Z ≫ ambientComparisonInv X Z = 𝟙 _ := sorry

/-- The named inverse followed by the ambient comparison is the identity. -/
@[stacks 0G70 "closed-subset ambient inverse comparison law"]
theorem ambientComparisonInv_comp :
    ambientComparisonInv X Z ≫ ambientComparison X Z = 𝟙 _ := sorry

/-- The explicit natural isomorphism associated to the closed-subset ambient comparison. -/
@[stacks 0G70 "closed-subset ambient global-sections natural isomorphism"]
noncomputable def ambientComparisonIso : derived X Z ≅ ambientDerived X Z where
  hom := ambientComparison X Z
  inv := ambientComparisonInv X Z
  hom_inv_id := ambientComparison_comp_inv X Z
  inv_hom_id := ambientComparisonInv_comp X Z

/-- The forward map of `GlobalSections.ambientComparisonIso` is the canonical comparison. -/
@[stacks 0G70 "closed-subset ambient natural isomorphism forward map"]
theorem ambientComparisonIso_hom :
    (ambientComparisonIso X Z).hom = ambientComparison X Z := sorry

/-- The inverse map of `GlobalSections.ambientComparisonIso` is the named inverse comparison. -/
@[stacks 0G70 "closed-subset ambient natural isomorphism inverse map"]
theorem ambientComparisonIso_inv :
    (ambientComparisonIso X Z).inv = ambientComparisonInv X Z := sorry

end AmbientComparison

end GlobalSections

namespace GlobalSectionsWithSupport

/-- Global sections of an ambient module sheaf supported on `Z`. -/
@[stacks 0G70 "module global sections with support"]
abbrev functor : X.Modules ⥤ ModuleCat (globalSectionsRing X) :=
  SectionsWithSupport.functor X Z ⋙ GlobalSections.functor X Z

/-- The cochain-level global-sections-with-support functor followed by localization. -/
@[stacks 0G70 "supported global-sections cochain localization"]
abbrev toDerived :
    CochainComplex X.Modules ℤ ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Functor.Derived.Cochain.toDerived (functor X Z)

/-- Total right-derived global sections with support in `Z`. -/
@[stacks 0G70 "derived module global sections with support"]
abbrev derived :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  Functor.RightDerived.Cochain.functor (functor X Z)

/-- The canonical unit for derived global sections with support. -/
@[stacks 0G70 "derived global-sections-with-support unit"]
abbrev unit :
    toDerived X Z ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙
        derived X Z :=
  Functor.RightDerived.Cochain.unit (functor X Z)

/-- The supported-global-sections unit, presented as a composite of cochain functors. -/
@[stacks 0G70 "supported global-sections comparison unit"]
abbrev comparisonUnit :
    (SectionsWithSupport.functor X Z).mapHomologicalComplex (up ℤ) ⋙
        GlobalSections.toDerived X Z ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙
        derived X Z :=
  unit X Z

/-- Derived global sections with support satisfy the right-derived universal property. -/
@[stacks 0G70 "derived global-sections-with-support universal property"]
noncomputable instance isRightDerived :
    (derived X Z).IsRightDerivedFunctor (unit X Z)
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) := sorry

/-- The composite-functor presentation of the supported-global-sections unit satisfies the same
right-derived universal property. -/
@[stacks 0G70 "supported global-sections comparison-unit universal property"]
noncomputable instance comparisonUnitIsRightDerived :
    (derived X Z).IsRightDerivedFunctor (comparisonUnit X Z)
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) := sorry

/-- Compute derived global sections with support by first deriving supported sections and then
deriving global sections on `Z`. -/
@[stacks 0G70 "derived global-sections-with-support model"]
abbrev model :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  SectionsWithSupport.derived X Z ⋙ GlobalSections.derived X Z

section Comparisons

variable [supportedComparisonDerived :
  (derived X Z).IsRightDerivedFunctor (comparisonUnit X Z)
    (HomologicalComplex.quasiIso X.Modules (up ℤ))]

/-- The universal comparison from derived global sections with support to the iterated derived
model. -/
@[stacks 0G70 "derived global-sections-with-support comparison"]
noncomputable def comparison : derived X Z ⟶ model X Z :=
  Functor.RightDerived.Composition.comparisonOfModels
    (F := (RingedSpace.ClosedSubset.SectionsWithSupport.functor X Z).mapHomologicalComplex
      (up ℤ))
    (G := GlobalSections.toDerived X Z)
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (SectionsWithSupport.unit X Z) (GlobalSections.unit X Z) (comparisonUnit X Z)

/-- The cochain-level unit whose universal-property lift is `comparison`. -/
@[stacks 0G70 "supported global-sections comparison unit"]
noncomputable abbrev modelUnit :
    (RingedSpace.ClosedSubset.SectionsWithSupport.functor X Z).mapHomologicalComplex
        (up ℤ) ⋙ GlobalSections.toDerived X Z ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙
        model X Z :=
  Functor.RightDerived.Composition.iteratedUnit
    (SectionsWithSupport.unit X Z) (GlobalSections.unit X Z)

/-- The supported comparison is characterized by its cochain-level factorization. -/
@[reassoc (attr := simp), stacks 0G70 "supported global-sections comparison factorization"]
theorem comparison_fac :
    comparisonUnit X Z ≫ Functor.whiskerLeft
        (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules)
        (comparison X Z) =
      modelUnit X Z := sorry

/-- The iterated ambient model for derived global sections with support. -/
@[stacks 0G70 "ambient iterated global-sections-with-support model"]
abbrev ambientModel :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat (globalSectionsRing X)) :=
  SectionsWithSupport.derived X Z ⋙ GlobalSections.ambientDerived X Z

variable [globalComparisonDerived :
  (GlobalSections.derived X Z).IsRightDerivedFunctor
    (GlobalSections.comparisonUnit X Z)
    (HomologicalComplex.quasiIso
      (RingedSpace.ClosedSubset.Modules X Z) (up ℤ))]

/-- The comparison from derived global sections with support to the ambient iterated model. -/
@[stacks 0G70 "ambient derived global-sections-with-support comparison"]
noncomputable def ambientComparison : derived X Z ⟶ ambientModel X Z :=
  comparison X Z ≫
    Functor.whiskerLeft (SectionsWithSupport.derived X Z)
      (GlobalSections.ambientComparison X Z)

/-- Forget support from the ambient iterated model. -/
@[stacks 0G70 "ambient global-sections forget-support map"]
noncomputable def ambientForget :
    ambientModel X Z ⟶ Module.Derived.GlobalSections.functor X :=
  (Functor.associator (SectionsWithSupport.derived X Z) (Pushforward.derived X Z)
      (Module.Derived.GlobalSections.functor X)).inv ≫
    Functor.whiskerRight (Derived.adjunction X Z).counit
      (Module.Derived.GlobalSections.functor X)

/-- Forget support before taking global sections. -/
@[stacks 0G70 "underived global-sections forget-support map"]
noncomputable def forget : functor X Z ⟶ moduleGlobalSectionsFunctor X :=
  (Functor.associator (SectionsWithSupport.functor X Z)
      (RingedSpace.ClosedSubset.pushforward X Z)
      (moduleGlobalSectionsFunctor X)).inv ≫
    Functor.whiskerRight
      (RingedSpace.ClosedSubset.SectionsWithSupport.adjunction X Z).counit
      (moduleGlobalSectionsFunctor X)

variable [supportedUnitDerived :
  (derived X Z).IsRightDerivedFunctor (unit X Z)
    (HomologicalComplex.quasiIso X.Modules (up ℤ))]
variable [globalUnitDerived :
  (Module.Derived.GlobalSections.functor X).IsRightDerivedFunctor
    (Module.Derived.GlobalSections.unit X)
    (HomologicalComplex.quasiIso X.Modules (up ℤ))]

/-- The canonical derived forget-support morphism. -/
@[stacks 0G70 "derived forget-support morphism"]
noncomputable def forgetDerived :
    derived X Z ⟶ Module.Derived.GlobalSections.functor X :=
  Functor.rightDerivedNatTrans
    (derived X Z) (Module.Derived.GlobalSections.functor X)
    (unit X Z) (Module.Derived.GlobalSections.unit X)
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (forget X Z) (up ℤ))
      (DerivedCategory.Q : CochainComplex (ModuleCat (globalSectionsRing X)) ℤ ⥤
        DerivedCategory (ModuleCat (globalSectionsRing X))))

/-- The canonical derived forget-support map is the ambient comparison followed by the
model-side counit. -/
@[stacks 0G70 "derived forget-support compatibility"]
theorem forgetDerived_eq :
    forgetDerived X Z = ambientComparison X Z ≫ ambientForget X Z := sorry

/-- The derived global-sections-with-support comparison is invertible. -/
@[stacks 0G70 "derived global-sections-with-support comparison isomorphism"]
noncomputable instance comparisonIsIso : IsIso (comparison X Z) := sorry

/-- The ambient derived global-sections-with-support comparison is invertible. -/
@[stacks 0G70 "ambient derived global-sections-with-support comparison isomorphism"]
noncomputable instance ambientComparisonIsIso : IsIso (ambientComparison X Z) := sorry

variable [comparisonIsoWitness : IsIso (comparison X Z)]
variable [ambientComparisonIsoWitness : IsIso (ambientComparison X Z)]

/-- The named inverse of the iterated derived global-sections-with-support comparison. -/
@[stacks 0G70 "inverse derived global-sections-with-support comparison"]
noncomputable def comparisonInv : model X Z ⟶ derived X Z :=
  CategoryTheory.inv (comparison X Z)

omit globalComparisonDerived supportedUnitDerived globalUnitDerived
    ambientComparisonIsoWitness in
/-- The iterated comparison followed by its named inverse is the identity. -/
@[stacks 0G70 "derived global-sections-with-support comparison inverse law"]
theorem comparison_comp_inv :
    comparison X Z ≫ comparisonInv X Z = 𝟙 _ := sorry

omit globalComparisonDerived supportedUnitDerived globalUnitDerived
    ambientComparisonIsoWitness in
/-- The named inverse followed by the iterated comparison is the identity. -/
@[stacks 0G70 "derived global-sections-with-support inverse comparison law"]
theorem comparisonInv_comp :
    comparisonInv X Z ≫ comparison X Z = 𝟙 _ := sorry

omit globalComparisonDerived supportedUnitDerived globalUnitDerived
    ambientComparisonIsoWitness in
/-- The explicit natural isomorphism associated to the iterated supported comparison. -/
@[stacks 0G70 "derived global-sections-with-support natural isomorphism"]
noncomputable def comparisonIso : derived X Z ≅ model X Z where
  hom := comparison X Z
  inv := comparisonInv X Z
  hom_inv_id := comparison_comp_inv X Z
  inv_hom_id := comparisonInv_comp X Z

omit globalComparisonDerived supportedUnitDerived globalUnitDerived
    ambientComparisonIsoWitness in
/-- The forward map of `comparisonIso` is the canonical iterated comparison. -/
@[stacks 0G70 "supported comparison natural isomorphism forward map"]
theorem comparisonIso_hom : (comparisonIso X Z).hom = comparison X Z := sorry

omit globalComparisonDerived supportedUnitDerived globalUnitDerived
    ambientComparisonIsoWitness in
/-- The inverse map of `comparisonIso` is the named inverse comparison. -/
@[stacks 0G70 "supported comparison natural isomorphism inverse map"]
theorem comparisonIso_inv : (comparisonIso X Z).inv = comparisonInv X Z := sorry

/-- The named inverse of the ambient derived global-sections-with-support comparison. -/
@[stacks 0G70 "inverse ambient global-sections-with-support comparison"]
noncomputable def ambientComparisonInv : ambientModel X Z ⟶ derived X Z :=
  CategoryTheory.inv (ambientComparison X Z)

omit comparisonIsoWitness supportedUnitDerived globalUnitDerived in
/-- The ambient comparison followed by its named inverse is the identity. -/
@[stacks 0G70 "ambient global-sections-with-support comparison inverse law"]
theorem ambientComparison_comp_inv :
    ambientComparison X Z ≫ ambientComparisonInv X Z = 𝟙 _ := sorry

omit comparisonIsoWitness supportedUnitDerived globalUnitDerived in
/-- The named inverse followed by the ambient comparison is the identity. -/
@[stacks 0G70 "ambient global-sections-with-support inverse comparison law"]
theorem ambientComparisonInv_comp :
    ambientComparisonInv X Z ≫ ambientComparison X Z = 𝟙 _ := sorry

omit comparisonIsoWitness supportedUnitDerived globalUnitDerived in
/-- The explicit natural isomorphism underlying `ambientComparison`. -/
@[stacks 0G70 "ambient global-sections comparison natural isomorphism"]
noncomputable def ambientComparisonIso : derived X Z ≅ ambientModel X Z where
  hom := ambientComparison X Z
  inv := ambientComparisonInv X Z
  hom_inv_id := ambientComparison_comp_inv X Z
  inv_hom_id := ambientComparisonInv_comp X Z

omit comparisonIsoWitness supportedUnitDerived globalUnitDerived in
/-- The forward map of `ambientComparisonIso` is the canonical ambient comparison. -/
@[stacks 0G70 "ambient comparison natural isomorphism forward map"]
theorem ambientComparisonIso_hom :
    (ambientComparisonIso X Z).hom = ambientComparison X Z := sorry

omit comparisonIsoWitness supportedUnitDerived globalUnitDerived in
/-- The inverse map of `ambientComparisonIso` is the named inverse comparison. -/
@[stacks 0G70 "ambient comparison natural isomorphism inverse map"]
theorem ambientComparisonIso_inv :
    (ambientComparisonIso X Z).inv = ambientComparisonInv X Z := sorry

end Comparisons

end GlobalSectionsWithSupport

/-- Scoped notation for global sections supported on a bundled closed subset. -/
scoped[RingedSpaceClosedSupport] notation3:max "Γₛ[" Z "]" =>
  AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.functor _ Z

/-- Scoped notation for derived global sections supported on a bundled closed subset. -/
scoped[RingedSpaceClosedSupport] notation3:max "RΓₛ[" Z "]" =>
  AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.derived _ Z

open scoped RingedSpaceClosedSupport

end AlgebraicGeometry.RingedSpace.ClosedSubset
