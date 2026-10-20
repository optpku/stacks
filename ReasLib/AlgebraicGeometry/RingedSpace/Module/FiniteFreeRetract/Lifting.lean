/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteFreeRetract.Exact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Local lifting from finite-free retract modules

The generic local-splitting owner applies to an epimorphism whose target is locally a finite-free
retract.  The API below packages its pullback-square consequence: a morphism whose source has
that property locally lifts through an arbitrary epimorphism.
-/

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules

variable {X : RingedSpace.{u}}

/-- A morphism `f : E ⟶ F` lifts through `p : G ⟶ F` on the open `U` after restriction to
`U`. -/
@[stacks 08C6 "restriction-level module lifting"]
def IsLiftableOn {E F G : X.Modules}
    (f : E ⟶ F) (p : G ⟶ F) (U : Opens X) : Prop :=
  ∃ l : (X.moduleRestrictionToOpen U).obj E ⟶
      (X.moduleRestrictionToOpen U).obj G,
    l ≫ (X.moduleRestrictionToOpen U).map p =
      (X.moduleRestrictionToOpen U).map f

/-- A morphism lifts locally through `p` at `x` when a restricted lift exists on some
neighborhood of `x`. -/
@[stacks 08C6 "point-neighborhood module lifting"]
def IsLocallyLiftableAt {E F G : X.Modules}
    (f : E ⟶ F) (p : G ⟶ F) (x : X) : Prop :=
  ∃ U : Opens X, x ∈ U ∧ IsLiftableOn f p U

/-- The point-local lifting predicate unfolds to its restricted-map equation. -/
theorem isLocallyLiftableAt_iff {E F G : X.Modules}
    (f : E ⟶ F) (p : G ⟶ F) (x : X) :
    IsLocallyLiftableAt f p x ↔
      ∃ U : Opens X, x ∈ U ∧
        ∃ l : (X.moduleRestrictionToOpen U).obj E ⟶
            (X.moduleRestrictionToOpen U).obj G,
          l ≫ (X.moduleRestrictionToOpen U).map p =
            (X.moduleRestrictionToOpen U).map f := sorry

namespace FiniteFreeRetract

/-- A morphism from a locally finite-free retract lifts locally through every epimorphism. -/
@[stacks 08C6 "local finite-free-retract source"]
theorem at_of_isLocal {E F G : X.Modules}
    [SheafOfModules.RingedSite.FiniteFreeRetract.IsLocal E]
    (f : E ⟶ F) (p : G ⟶ F) [Epi p] (x : X) :
    IsLocallyLiftableAt f p x := sorry

/-- A morphism from a locally finite-free retract lifts through an epimorphism after restriction
to the members of an open cover. -/
@[stacks 08C6 "local finite-free-retract source, cover view"]
theorem cover_of_isLocal {E F G : X.Modules}
    [SheafOfModules.RingedSite.FiniteFreeRetract.IsLocal E]
    (f : E ⟶ F) (p : G ⟶ F) [Epi p] :
    ∃ (I : Type u) (U : I → Opens X), IsOpenCover U ∧
      ∀ i : I, IsLiftableOn f p (U i) := sorry

/-- Lemma 20.46.5: a morphism from a finite-free retract module lifts locally through every
epimorphism. -/
@[stacks 08C6 "finite-free-retract source"]
theorem at_of_property {E F G : X.Modules}
    (hE : SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf E)
    (f : E ⟶ F) (p : G ⟶ F) [Epi p] (x : X) :
    IsLocallyLiftableAt f p x := sorry

/-- Lemma 20.46.5, open-cover form. -/
@[stacks 08C6 "finite-free-retract source, cover view"]
theorem cover_of_property {E F G : X.Modules}
    (hE : SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf E)
    (f : E ⟶ F) (p : G ⟶ F) [Epi p] :
    ∃ (I : Type u) (U : I → Opens X), IsOpenCover U ∧
      ∀ i : I, IsLiftableOn f p (U i) := sorry

end FiniteFreeRetract

end AlgebraicGeometry.RingedSpace.Modules
