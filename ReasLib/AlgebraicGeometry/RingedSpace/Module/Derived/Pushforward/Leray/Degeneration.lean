module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Leray.Degeneration
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Underlying.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degeneration of the ringed-space Leray spectral sequence

These are the opens-ringed-site specializations of the single-row and single-column
Grothendieck degeneration criteria.  Their surface uses the canonical underlying-sheaf global
cohomology and higher-direct-image owners.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry RingedSpace.Hom
open RingedSpace.Module.Derived.Sections.Underlying

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleLeray.Degeneration

variable {X Y : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]

/-- The single-row Leray degeneration criterion in its canonical right-derived vanishing form. -/
@[stacks 01F4 "single-row Leray degeneration from derived vanishing"]
theorem rowOfVanishes (f : X ⟶ Y) (F : X.Modules)
    (hRq : Functor.RightDerived.Vanishes.aboveZero (pushforward f) F)
    (p : ℕ) :
    IsIsomorphic (globalCohomology F p)
      (globalCohomology ((pushforward f).obj F) p) := sorry

/-- Lemma 20.13.6 (1): if all positive higher direct images vanish, source global cohomology is
isomorphic to global cohomology of the ordinary direct image. -/
@[stacks 01F4 "single-row Leray degeneration"]
theorem row (f : X ⟶ Y) (F : X.Modules)
    (hRq : ∀ q : ℕ, 0 < q → IsZero (higherDirectImageModule f F q))
    (p : ℕ) :
    IsIsomorphic (globalCohomology F p)
      (globalCohomology ((pushforward f).obj F) p) := sorry

/-- Lemma 20.13.6 (2): if every higher direct image has vanishing positive target cohomology,
source global cohomology is isomorphic to degree-zero cohomology of that higher direct image. -/
@[stacks 01F4 "single-column Leray degeneration"]
theorem column (f : X ⟶ Y) (F : X.Modules)
    (hHp : ∀ q p : ℕ, 0 < p →
      IsZero (globalCohomology (higherDirectImageModule f F q) p))
    (q : ℕ) :
    IsIsomorphic (globalCohomology F q)
      (globalCohomology (higherDirectImageModule f F q) 0) := sorry

end AlgebraicGeometry.RingedSpace.ModuleLeray.Degeneration
