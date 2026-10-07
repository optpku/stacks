module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ClosedSubset.SectionsWithSupport
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived module functors for a closed subspace

For a sheaf of rings `𝒪` and a bundled closed subset `Z`, this file owns the derived category of
modules on `Z`, the exact derived direct image, and the total right derived functor of sections
supported on `Z`. It also records the derived adjunction, obtained by comparing the exact direct
image with its total left-derived presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules.ClosedSubset

variable {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u}) (Z : Closeds X)

/-- The unbounded derived category of module sheaves on a bundled closed subspace. -/
@[stacks 0A3B "closed-subset module derived category"]
abbrev ModuleDerived [HasDerivedCategory (Modules 𝒪 Z)] :=
  DerivedCategory (Modules 𝒪 Z)

namespace Derived

variable [HasDerivedCategory (SheafOfModules 𝒪)]
variable [HasDerivedCategory (Modules 𝒪 Z)]

/-- The derived direct image from a bundled closed subspace, induced by exact pushforward. -/
@[stacks 0A3B "derived closed-subset pushforward"]
noncomputable abbrev pushforward :
    ModuleDerived 𝒪 Z ⥤ DerivedCategory (SheafOfModules 𝒪) :=
  (ClosedSubset.pushforward 𝒪 Z).mapDerivedCategory

/-- The canonical localization square comparing derived and cochain-level closed-subset
pushforward. -/
@[stacks 0A3B "derived closed-subset pushforward comparison"]
noncomputable abbrev pushforwardFactors :
    (DerivedCategory.Q : CochainComplex (Modules 𝒪 Z) ℤ ⥤ ModuleDerived 𝒪 Z) ⋙
        pushforward 𝒪 Z ≅
      Functor.Derived.Cochain.toDerived (ClosedSubset.pushforward 𝒪 Z) :=
  (ClosedSubset.pushforward 𝒪 Z).mapDerivedCategoryFactors

/-- The cochain-level closed-subset pushforward followed by localization. -/
@[stacks 0A3B "cochain-level closed-subset pushforward localization"]
abbrev pushforwardToDerived :
    CochainComplex (Modules 𝒪 Z) ℤ ⥤ DerivedCategory (SheafOfModules 𝒪) :=
  Functor.Derived.Cochain.toDerived (ClosedSubset.pushforward 𝒪 Z)

/-- Exact derived direct image commutes with embedding an object as a complex concentrated in
one degree. -/
@[stacks 0A3B "derived closed-subset pushforward of a single object"]
noncomputable def pushforwardSingleFunctorIso (M : Modules 𝒪 Z) (n : ℤ) :
    (pushforward 𝒪 Z).obj
        ((DerivedCategory.singleFunctor (Modules 𝒪 Z) n).obj M) ≅
      (DerivedCategory.singleFunctor (SheafOfModules 𝒪) n).obj
        ((ClosedSubset.pushforward 𝒪 Z).obj M) :=
  ((ClosedSubset.pushforward 𝒪 Z).mapDerivedCategorySingleFunctor n).app M

/-- The cochain-level supported-sections functor followed by localization. -/
@[stacks 0A3B "cochain-level supported-sections localization"]
abbrev sectionsWithSupportToDerived :
    CochainComplex (SheafOfModules 𝒪) ℤ ⥤ ModuleDerived 𝒪 Z :=
  Functor.Derived.Cochain.toDerived (SectionsWithSupport.functor 𝒪 Z)

/-- The total right derived functor of module sections supported on a bundled closed subset. -/
@[stacks 0A3B "derived module sections with support"]
noncomputable abbrev sectionsWithSupport :
    DerivedCategory (SheafOfModules 𝒪) ⥤ ModuleDerived 𝒪 Z :=
  Functor.RightDerived.Cochain.functor
    (SectionsWithSupport.functor 𝒪 Z)

/-- The canonical cochain-level unit from supported sections to its total right derived functor. -/
@[stacks 0A3B "derived supported-sections unit"]
noncomputable abbrev sectionsWithSupportUnit :
    sectionsWithSupportToDerived 𝒪 Z ⟶
      (DerivedCategory.Q : CochainComplex (SheafOfModules 𝒪) ℤ ⥤
        DerivedCategory (SheafOfModules 𝒪)) ⋙ sectionsWithSupport 𝒪 Z :=
  Functor.RightDerived.Cochain.unit
    (SectionsWithSupport.functor 𝒪 Z)

/-- The adjunction between direct image and supported sections, applied termwise to cochain
complexes. -/
@[stacks 0A3B "cochain adjunction for a closed subset"]
noncomputable abbrev cochainAdjunction :
    (ClosedSubset.pushforward 𝒪 Z).mapHomologicalComplex (up ℤ) ⊣
      (SectionsWithSupport.functor 𝒪 Z).mapHomologicalComplex (up ℤ) :=
  CategoryTheory.Adjunction.mapHomologicalComplexAdjunction
    (SectionsWithSupport.adjunction 𝒪 Z) (up ℤ)

/-- The total left-derived presentation of exact direct image from a closed subset. -/
@[stacks 0A3B "total left-derived closed-subset pushforward"]
noncomputable abbrev pushforwardTotalLeft :
    ModuleDerived 𝒪 Z ⥤ DerivedCategory (SheafOfModules 𝒪) :=
  (pushforwardToDerived 𝒪 Z).totalLeftDerived
    (DerivedCategory.Q : CochainComplex (Modules 𝒪 Z) ℤ ⥤ ModuleDerived 𝒪 Z)
    (HomologicalComplex.quasiIso (Modules 𝒪 Z) (up ℤ))

/-- The canonical comparison from the total left-derived presentation of direct image to its
cochain-level functor. -/
@[stacks 0A3B "total left-derived pushforward counit"]
noncomputable abbrev pushforwardTotalLeftCounit :
    (DerivedCategory.Q : CochainComplex (Modules 𝒪 Z) ℤ ⥤ ModuleDerived 𝒪 Z) ⋙
        pushforwardTotalLeft 𝒪 Z ⟶
      pushforwardToDerived 𝒪 Z :=
  (pushforwardToDerived 𝒪 Z).totalLeftDerivedCounit
    (DerivedCategory.Q : CochainComplex (Modules 𝒪 Z) ℤ ⥤ ModuleDerived 𝒪 Z)
    (HomologicalComplex.quasiIso (Modules 𝒪 Z) (up ℤ))

/-- The total and exact presentations of derived direct image are canonically isomorphic. -/
@[stacks 0A3B "total-left and exact direct-image comparison"]
noncomputable abbrev pushforwardTotalLeftIso :
    pushforwardTotalLeft 𝒪 Z ≅ pushforward 𝒪 Z :=
  Functor.leftDerivedUnique
    (LF := pushforwardTotalLeft 𝒪 Z)
    (LF' := pushforward 𝒪 Z)
    (α := pushforwardTotalLeftCounit 𝒪 Z)
    (α'₂ := (pushforwardFactors 𝒪 Z).hom)
    (HomologicalComplex.quasiIso (Modules 𝒪 Z) (up ℤ))

/-- The cochain adjunction has the absolute derived-pair property needed to derive both sides
simultaneously. This is a property of the chosen derived presentations, not additional data. -/
@[stacks 0A3B "cochain closed-subset adjunction derived pair"]
noncomputable instance cochainAdjunctionHasPair :
    CategoryTheory.Adjunction.TotalDerived.HasPair
      (G := (ClosedSubset.pushforward 𝒪 Z).mapHomologicalComplex (up ℤ))
      (F := (SectionsWithSupport.functor 𝒪 Z).mapHomologicalComplex (up ℤ))
      (HomologicalComplex.quasiIso (Modules 𝒪 Z) (up ℤ))
      (HomologicalComplex.quasiIso (SheafOfModules 𝒪) (up ℤ))
      (L1 := DerivedCategory.Q) (L2 := DerivedCategory.Q) := sorry

/-- The canonical adjunction between exact derived direct image and derived sections supported
on a bundled closed subset. -/
@[stacks 0A3B "derived closed-subset adjunction"]
noncomputable def adjunction :
    pushforward 𝒪 Z ⊣ sectionsWithSupport 𝒪 Z :=
  (CategoryTheory.Adjunction.TotalDerived.HasPair.derived
      (cochainAdjunction 𝒪 Z)
      (HomologicalComplex.quasiIso (Modules 𝒪 Z) (up ℤ))
      (HomologicalComplex.quasiIso (SheafOfModules 𝒪) (up ℤ))).ofNatIsoLeft
    (pushforwardTotalLeftIso 𝒪 Z)

/-- The unit of the derived direct-image/supported-sections adjunction is invertible. -/
@[stacks 0A3B "derived closed-subset adjunction unit"]
noncomputable instance adjunctionUnitIsIso : IsIso (adjunction 𝒪 Z).unit := sorry

/-- Exact derived direct image from a closed subset is fully faithful. -/
@[stacks 0A3B "derived closed-subset direct image is fully faithful"]
noncomputable def pushforwardFullyFaithful : (pushforward 𝒪 Z).FullyFaithful :=
  (adjunction 𝒪 Z).fullyFaithfulLOfIsIsoUnit

/-- Derived direct image from a bundled closed subspace is full. -/
@[stacks 0A3B "derived closed-subset pushforward full"]
noncomputable instance pushforwardFull : Functor.Full (pushforward 𝒪 Z) :=
  (pushforwardFullyFaithful 𝒪 Z).full

/-- Derived direct image from a bundled closed subspace is faithful. -/
@[stacks 0A3B "derived closed-subset pushforward faithful"]
noncomputable instance pushforwardFaithful : Functor.Faithful (pushforward 𝒪 Z) :=
  (pushforwardFullyFaithful 𝒪 Z).faithful

end Derived

end SheafOfModules.ClosedSubset
