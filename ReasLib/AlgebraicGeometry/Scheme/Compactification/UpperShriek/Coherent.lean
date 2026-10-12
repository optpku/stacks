/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coherent.Quasicoherent

@[expose] public section

open CategoryTheory
open CategoryTheory.StructuredArrow
open DerivedCategory.Plus
open DerivedCategory.Plus.CohomologyIn
open RingedSpace
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Compactification
namespace Of

/-- A bounded-below upper-shriek model sends coherent-cohomology inputs to
objects with coherent cohomology. -/
theorem upperShriek_coherent
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (a : DerivedQCoh (Over.left Y.obj) ⥤ DerivedQCoh (Over.left (right P.obj)))
    (aAdjunction : DerivedQCoh.pushforwardCohomologyIn (Over.hom (right P.obj)) ⊣ a)
    (aPlus : DerivedQCoh.Plus (Over.left Y.obj) ⥤
      DerivedQCoh.Plus (Over.left (right P.obj)))
    (aPlusCompatibility :
      aPlus ⋙ ambient (quasiCoherentModuleProperty (Over.left (right P.obj))) ≅
        toUnbounded (quasiCoherentModuleProperty (Over.left Y.obj)) ⋙
          a ⋙ DerivedQCoh.inclusion (Over.left (right P.obj)))
    (K : D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]) :
    (DerivedCategory.Plus.cohomologyIn
      (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf))
      (((DerivedQCoh.coherentPlusInclusion (Over.left Y.obj) ⋙ upperShriek f P aPlus) ⋙
        (DerivedCategory.Plus.cohomologyIn
          (quasiCoherentModuleProperty (Over.left X.obj))).ι).obj K) := sorry

/-- The bounded-below upper-shriek model restricted to coherent cohomology. -/
noncomputable def upperShriekCoherentPlus
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (a : DerivedQCoh (Over.left Y.obj) ⥤ DerivedQCoh (Over.left (right P.obj)))
    (aAdjunction : DerivedQCoh.pushforwardCohomologyIn (Over.hom (right P.obj)) ⊣ a)
    (aPlus : DerivedQCoh.Plus (Over.left Y.obj) ⥤
      DerivedQCoh.Plus (Over.left (right P.obj)))
    (aPlusCompatibility :
      aPlus ⋙ ambient (quasiCoherentModuleProperty (Over.left (right P.obj))) ≅
        toUnbounded (quasiCoherentModuleProperty (Over.left Y.obj)) ⋙
          a ⋙ DerivedQCoh.inclusion (Over.left (right P.obj))) :
    D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf] ⥤
      D⁺[SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf] :=
  (DerivedCategory.Plus.cohomologyIn.{u + 1}
    (SheafOfModules.isCoherent (Over.left X.obj).ringCatSheaf)).lift
      ((DerivedQCoh.coherentPlusInclusion (Over.left Y.obj) ⋙ upperShriek f P aPlus) ⋙
        (DerivedCategory.Plus.cohomologyIn
          (quasiCoherentModuleProperty (Over.left X.obj))).ι)
      (upperShriek_coherent f P a aAdjunction aPlus aPlusCompatibility)

/-- The underlying object of the coherent upper-shriek restriction agrees with
the underlying upper-shriek object after coherent inclusion. -/
theorem upperShriekCoherentPlus_obj_obj
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
    (a : DerivedQCoh (Over.left Y.obj) ⥤ DerivedQCoh (Over.left (right P.obj)))
    (aAdjunction : DerivedQCoh.pushforwardCohomologyIn (Over.hom (right P.obj)) ⊣ a)
    (aPlus : DerivedQCoh.Plus (Over.left Y.obj) ⥤
      DerivedQCoh.Plus (Over.left (right P.obj)))
    (aPlusCompatibility :
      aPlus ⋙ ambient (quasiCoherentModuleProperty (Over.left (right P.obj))) ≅
        toUnbounded (quasiCoherentModuleProperty (Over.left Y.obj)) ⋙
          a ⋙ DerivedQCoh.inclusion (Over.left (right P.obj)))
    (K : D⁺[SheafOfModules.isCoherent (Over.left Y.obj).ringCatSheaf]) :
    ((upperShriekCoherentPlus f P a aAdjunction aPlus aPlusCompatibility).obj K).obj =
      ((upperShriek f P aPlus).obj
        ((DerivedQCoh.coherentPlusInclusion (Over.left Y.obj)).obj K)).obj := sorry

end Of
end Compactification
end Scheme
end AlgebraicGeometry
