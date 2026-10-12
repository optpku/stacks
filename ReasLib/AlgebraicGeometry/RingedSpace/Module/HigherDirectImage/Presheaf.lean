/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage.Underlying
public import ReasLib.Topology.Sheaf.HigherDirectImage.Presheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology-presheaf model of higher direct images

This file combines the underlying-additive comparison for module higher direct images with the
canonical sheafification model for higher direct images of additive sheaves.  The module-valued
and additive comparisons remain separate owners; this leaf is their ringed-space specialization.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.Presheaf

variable {X Y : RingedSpace.{u}}

/-- The functorial underlying-additive comparison for all coefficient modules. -/
@[stacks 01E4 "functorial underlying higher direct image from the cohomology presheaf"]
theorem functor_isomorphic_sheafification
    (f : X ⟶ Y) (p : ℕ) :
    IsIsomorphic
      (higherDirectImageModuleFunctor f p ⋙ moduleUnderlyingSheaf Y)
      (moduleUnderlyingSheaf X ⋙
        TopCat.Sheaf.HigherDirectImage.Presheaf.sheafifiedCohomologyFunctor
          f.hom.base p) := sorry

/-- Lemma 20.7.3 (01E4): the underlying additive sheaf of a module higher direct image is
isomorphic to the sheafification of the pushed-forward cohomology presheaf. -/
@[stacks 01E4 "underlying higher direct image from the cohomology presheaf"]
theorem underlying_isomorphic_sheafification
    (f : X ⟶ Y) (F : X.Modules) (p : ℕ) :
    IsIsomorphic
      ((moduleUnderlyingSheaf Y).obj (higherDirectImageModule f F p))
      ((presheafToSheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}).obj
        ((Opens.map f.hom.base).op ⋙
          ((moduleUnderlyingSheaf X).obj F).cohomologyPresheaf p)) := sorry

/-- Positive cohomology presheaves become zero after sheafification. -/
@[stacks 03BA "positive cohomology presheaf sheafification vanishing"]
theorem isZero_sheafification_of_pos
    (X : RingedSpace.{u}) (F : X.Modules) {p : ℕ} (hp : 0 < p) :
    IsZero
      ((presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (((moduleUnderlyingSheaf X).obj F).cohomologyPresheaf p)) := sorry

end AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.Presheaf
