/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ClosedSubset.Derived
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Support
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Coreflective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived module sheaves supported on a closed subset

For a sheaf of rings `𝒪` and a bundled closed subset `Z`, derived direct image identifies the
derived category on `Z` with the full subcategory of ambient derived modules whose cohomology is
supported on `Z`.  The resulting inclusion is coreflective, with coreflector obtained from derived
sections with support followed by the lifted direct image.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules.ClosedSubset

variable {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u}) (Z : Closeds X)
variable [HasDerivedCategory (SheafOfModules 𝒪)] [HasDerivedCategory (Modules 𝒪 Z)]

/-- The full subcategory of ambient derived modules whose cohomology is supported on `Z`. -/
@[stacks 0AEF "derived modules supported on a closed subset"]
abbrev SupportedDerived :=
  DerivedCategory.CohomologyIn
    (SheafOfModules.supportedOn (𝒪 := 𝒪) (Z : Set X))

namespace SupportedDerived

/-- The inclusion of derived modules supported on `Z` into the ambient derived category. -/
@[stacks 0AEF "inclusion of supported derived modules"]
abbrev inclusion :
    SupportedDerived 𝒪 Z ⥤ DerivedCategory (SheafOfModules 𝒪) :=
  (DerivedCategory.cohomologyIn
    (SheafOfModules.supportedOn (𝒪 := 𝒪) (Z : Set X))).ι

end SupportedDerived

namespace Derived.Pushforward

/-- An ambient derived module is in the essential image of closed-subset direct image exactly
when all of its cohomology sheaves are supported on the closed subset. -/
@[stacks 0AEF "essential image of derived closed-subset pushforward"]
theorem mem_essImage_iff_supported
    (K : DerivedCategory (SheafOfModules 𝒪)) :
    (Derived.pushforward 𝒪 Z).essImage K ↔
      DerivedCategory.cohomologyIn
        (SheafOfModules.supportedOn (𝒪 := 𝒪) (Z : Set X)) K := sorry

/-- Derived direct image from `Z` has cohomology supported on `Z`. -/
@[stacks 0AEF "derived closed-subset pushforward has supported cohomology"]
theorem obj_supported (K : ModuleDerived 𝒪 Z) :
    DerivedCategory.cohomologyIn
      (SheafOfModules.supportedOn (𝒪 := 𝒪) (Z : Set X))
      ((Derived.pushforward 𝒪 Z).obj K) := sorry

/-- Derived direct image lifted to the full subcategory of derived modules supported on `Z`. -/
@[stacks 0AEF "derived pushforward to the supported subcategory"]
noncomputable abbrev toSupported :
    ModuleDerived 𝒪 Z ⥤ SupportedDerived 𝒪 Z :=
  (DerivedCategory.cohomologyIn
    (SheafOfModules.supportedOn (𝒪 := 𝒪) (Z : Set X))).lift
      (Derived.pushforward 𝒪 Z) (obj_supported 𝒪 Z)

/-- Forgetting the support witness after lifted direct image recovers derived direct image. -/
@[stacks 0AEF "supported pushforward inclusion comparison"]
noncomputable def toSupportedCompιIso :
    toSupported 𝒪 Z ⋙ SupportedDerived.inclusion 𝒪 Z ≅
      Derived.pushforward 𝒪 Z :=
  (DerivedCategory.cohomologyIn
    (SheafOfModules.supportedOn (𝒪 := 𝒪) (Z : Set X))).liftCompιIso
      (Derived.pushforward 𝒪 Z) (obj_supported 𝒪 Z)

/-- Lifted derived direct image is an equivalence onto the supported derived subcategory. -/
@[stacks 0AEF "derived closed-subset pushforward equivalence"]
noncomputable instance toSupported_isEquivalence :
    (toSupported 𝒪 Z).IsEquivalence := sorry

end Derived.Pushforward

namespace SupportedDerived

/-- The coreflector onto derived modules supported on `Z`: take derived sections with support and
then apply lifted derived direct image. -/
@[stacks 0AEF "coreflector onto supported derived modules"]
noncomputable def coreflector :
    DerivedCategory (SheafOfModules 𝒪) ⥤ SupportedDerived 𝒪 Z :=
  Derived.sectionsWithSupport 𝒪 Z ⋙ Derived.Pushforward.toSupported 𝒪 Z

/-- The inclusion of derived modules supported on `Z` is left adjoint to the supported-sections
coreflector. -/
@[stacks 0AEF "coreflection onto supported derived modules"]
noncomputable def adjunction :
    inclusion 𝒪 Z ⊣ coreflector 𝒪 Z :=
  CategoryTheory.ObjectProperty.FullSubcategory.inclusionAdjunctionOfLift
    (Derived.adjunction 𝒪 Z) (Derived.Pushforward.obj_supported 𝒪 Z)

/-- Derived modules supported on `Z` form a coreflective full subcategory of ambient derived
modules. -/
@[stacks 0AEF "supported derived modules form a coreflective subcategory"]
noncomputable instance inclusionCoreflective : Coreflective (inclusion 𝒪 Z) where
  R := coreflector 𝒪 Z
  adj := adjunction 𝒪 Z

end SupportedDerived

end SheafOfModules.ClosedSubset
