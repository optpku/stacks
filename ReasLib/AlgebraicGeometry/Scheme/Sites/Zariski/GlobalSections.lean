/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.UniverseLift
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import ReasLib.Algebra.Category.Ring.Limits

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Zariski.Small

/-- The identity open immersion, as an object of the small Zariski site. -/
private def terminalOpen (S : Scheme.{u}) : S.smallZariskiSite :=
  MorphismProperty.Over.mk _ (𝟙 S) inferInstance

/-- The identity open immersion is terminal in the small Zariski site. -/
private def terminalOpenIsTerminal (S : Scheme.{u}) : IsTerminal (terminalOpen S) :=
  isLimitOfReflects (MorphismProperty.Over.forget @IsOpenImmersion ⊤ S)
    ((isLimitMapConeEmptyConeEquiv
      (MorphismProperty.Over.forget @IsOpenImmersion ⊤ S) (terminalOpen S)).symm Over.mkIdTerminal)

/-- Small-Zariski global functions identify with the universe lift of the scheme's global functions by terminal evaluation. -/
def globalFunctionsIso (S : Scheme.{u}) :
    RingedSite.Hom.globalSectionsRing (AssociatedModule.smallCommRingedSite .zariski S) ≃+*
      ULift.{u + 1} Γ(S, ⊤) :=
  (IsLimit.conePointUniqueUpToIso
    (limit.isLimit (AssociatedModule.smallCommRingedSite .zariski S).structureSheaf.obj)
      (limitOfDiagramInitial (terminalOpenIsTerminal S).op
        (AssociatedModule.smallCommRingedSite .zariski S).structureSheaf.obj)).ringCatIsoToRingEquiv

/-- Terminal evaluation and its inverse identify small-Zariski sections with global functions and their restrictions. -/
theorem globalFunctionsIso_spec (S : Scheme.{u}) :
    (∀ a, globalFunctionsIso S a =
      (limit.π (AssociatedModule.smallCommRingedSite .zariski S).structureSheaf.obj
        (op (terminalOpen S))) a) ∧
    (∀ (a : ULift.{u + 1} Γ(S, ⊤)) (U : S.smallZariskiSite),
      (limit.π (AssociatedModule.smallCommRingedSite .zariski S).structureSheaf.obj (op U))
        ((globalFunctionsIso S).symm a) = ULift.up (Scheme.Hom.appTop U.hom a.down)) := sorry

end AlgebraicGeometry.Scheme.Zariski.Small
