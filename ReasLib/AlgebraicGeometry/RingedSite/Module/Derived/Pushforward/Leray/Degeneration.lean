/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Leray
public import ReasLib.AlgebraicGeometry.RingedSite.Module.HigherDirectImage

/-!
# Degeneration of Leray spectral sequences

The two standard Leray degeneration criteria are the degree-zero module specializations of the
single-row and single-column Grothendieck API.  Their conclusions use the canonical module
global-cohomology and higher-direct-image owners.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom.Leray.Degeneration

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [EnoughInjectives (ModuleCat.{w} X)] [EnoughInjectives (ModuleCat.{w} Y)]
variable [HasExt (ModuleCat.{w} X)] [HasExt (ModuleCat.{w} Y)]

/-- Under the abstract Leray acyclicity condition, vanishing positive higher direct images
identifies source cohomology with cohomology of the ordinary direct image. -/
@[stacks 0733 "(1), abstract acyclicity"]
theorem rowOfAcyclic (f : Hom X Y)
    [HasWeakSheafify Y.siteTopology AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{w}]
    (h : Leray.IsAcyclic f) (ℱ : ModuleCat.{w} X)
    (hRq : Functor.RightDerived.Vanishes.aboveZero f.modulePushforward ℱ) (p : ℕ) :
    IsIsomorphic (moduleGlobalCohomology X ℱ p)
      (moduleGlobalCohomology Y (f.modulePushforward.obj ℱ) p) := sorry

/-- Under the abstract Leray acyclicity condition, vanishing positive target cohomology of the
higher direct images identifies source cohomology with degree-zero target cohomology. -/
@[stacks 0733 "(2), abstract acyclicity"]
theorem columnOfAcyclic (f : Hom X Y)
    [HasWeakSheafify Y.siteTopology AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{w}]
    (h : Leray.IsAcyclic f) (ℱ : ModuleCat.{w} X)
    (hHp : ∀ q p : ℕ, 0 < p →
      IsZero (moduleGlobalCohomology Y (higherDirectImageModule f ℱ q) p)) (q : ℕ) :
    IsIsomorphic (moduleGlobalCohomology X ℱ q)
      (moduleGlobalCohomology Y (higherDirectImageModule f ℱ q) 0) := sorry

/-- Stacks 0733 (1): if the positive higher direct images vanish, the single-row Leray spectral
sequence identifies source cohomology with cohomology of the ordinary direct image. -/
@[stacks 0733 "(1), single-row Leray degeneration"]
theorem row (f : Hom X Y)
    [HasSheafify Y.siteTopology AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{w}]
    [HasExt (Sheaf Y.siteTopology AddCommGrpCat.{w})]
    (ℱ : ModuleCat.{w} X)
    (hRq : Functor.RightDerived.Vanishes.aboveZero f.modulePushforward ℱ) (p : ℕ) :
    IsIsomorphic (moduleGlobalCohomology X ℱ p)
      (moduleGlobalCohomology Y (f.modulePushforward.obj ℱ) p) := sorry

/-- Stacks 0733 (2): if all positive target cohomology of the higher direct images vanishes, the
single-column Leray spectral sequence identifies source cohomology with degree-zero target
cohomology. -/
@[stacks 0733 "(2), single-column Leray degeneration"]
theorem column (f : Hom X Y)
    [HasSheafify Y.siteTopology AddCommGrpCat.{w}]
    [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{w}]
    [HasExt (Sheaf Y.siteTopology AddCommGrpCat.{w})]
    (ℱ : ModuleCat.{w} X)
    (hHp : ∀ q p : ℕ, 0 < p →
      IsZero (moduleGlobalCohomology Y (higherDirectImageModule f ℱ q) p)) (q : ℕ) :
    IsIsomorphic (moduleGlobalCohomology X ℱ q)
      (moduleGlobalCohomology Y (higherDirectImageModule f ℱ q) 0) := sorry

end RingedSite.Hom.Leray.Degeneration
