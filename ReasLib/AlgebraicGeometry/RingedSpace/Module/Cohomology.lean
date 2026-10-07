module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

/-!
# Cohomology of module sheaves on ringed spaces

This leaf gives a compact ringed-space interface to Mathlib's sheaf
cohomology object `Sheaf.H'`.  It keeps the choice of an open set explicit
and provides the top-open specialization used for ordinary cohomology.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The `p`th sheaf cohomology object of a module sheaf on an open subset of
a ringed space. -/
abbrev moduleCohomologyOnOpen
    (F : Modules X) (p : ℕ) (U : Opens X) : AddCommGrpCat :=
  ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H' p U

/-- The `p`th cohomology object of a module sheaf on the whole ringed space. -/
abbrev moduleCohomology (F : Modules X) (p : ℕ) : AddCommGrpCat :=
  moduleCohomologyOnOpen F p (⊤ : Opens X)

end AlgebraicGeometry.RingedSpace
