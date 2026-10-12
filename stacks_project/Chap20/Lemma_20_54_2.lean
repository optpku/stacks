/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage.ProjectionFormula
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.ProjectionFormula
import StacksCheckRecall

@[expose] public section

/- Lemma 20.54.2 (1): for a finite locally free `𝒪_Y`-module `E`, tensoring by `E`
commutes up to isomorphism with every higher direct image `R^q f_*`. -/
@[stacks 01E8 "(1)"]
#check @AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.projectionFormula

/- Lemma 20.54.2 (2): on derived modules, the canonical projection-formula maps assemble into
a functorial isomorphism; restricting to `D⁺(𝒪_X)` gives the source formulation. -/
@[stacks 01E8 "(2)"]
#check @SheafOfModules.IsFiniteLocallyFree.projectionFormulaNatIso
