module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of strictly perfect complexes on ringed spaces

This leaf specializes the site-theoretic pullback theorem to the canonical opens sites of ringed
spaces. All continuity, finality, and sheafification inputs are supplied by global instances.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex

variable {X Y : RingedSpace.{u}}

/-- Lemma 20.46.4: pullback along a morphism of ringed spaces preserves strictly perfect
complexes of modules. -/
@[stacks 09U6]
theorem isStrictlyPerfect_pullback (f : X ⟶ Y)
    (E : _root_.CochainComplex Y.Modules ℤ)
    (hE : SheafOfModules.CochainComplex.IsStrictlyPerfect E) :
    SheafOfModules.CochainComplex.IsStrictlyPerfect
      (((RingedSpace.Hom.pullback f).mapHomologicalComplex (up ℤ)).obj E) := sorry

end AlgebraicGeometry.RingedSpace.CochainComplex
