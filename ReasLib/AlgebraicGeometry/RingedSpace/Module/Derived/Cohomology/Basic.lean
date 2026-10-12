/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomology sheaves of derived modules on ringed spaces

This is the lightweight owner for cohomology objects and their induced maps.  Stalk, finiteness,
and open-section APIs import this leaf instead of owning the underlying cohomology sheaf.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- The degree-`i` cohomology sheaf of a derived `𝒪_X`-module. -/
@[stacks 0GTA "cohomology sheaf"]
abbrev cohomologySheaf (E : ModuleDerived X) (i : ℤ) : X.Modules :=
  (DerivedCategory.homologyFunctor X.Modules i).obj E

/-- The map on degree-`i` cohomology sheaves induced by a morphism of derived modules. -/
abbrev cohomologySheafMap {E F : ModuleDerived X} (f : E ⟶ F) (i : ℤ) :
    cohomologySheaf E i ⟶ cohomologySheaf F i :=
  (DerivedCategory.homologyFunctor X.Modules i).map f

end AlgebraicGeometry.RingedSpace.ModuleDerived
