/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CardinalGeneration
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable (X : RingedSpace.{u})

/- Definition 28.23.1: a sheaf of `𝒪_X`-modules is `κ`-generated if it is generated on
an open cover by families of sections of cardinality at most `κ`. -/
@[stacks 077L] #check
  (SheafOfModules.IsKappaGenerated : X.Modules → Cardinal.{u} → Prop)
