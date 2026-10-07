module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology

/-!
# Maps on module cohomology

This leaf owns the additive map on cohomology induced by a morphism of module
sheaves.  The object and map owners are separated so applications that only
need functoriality do not import derived or scheme-specific infrastructure.
-/

@[expose] public section

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The map on degree-`p` module cohomology induced by a module morphism. -/
noncomputable abbrev moduleCohomologyMap
    {F G : X.Modules} (φ : F ⟶ G) (p : ℕ) :
    moduleCohomology F p ⟶ moduleCohomology G p :=
  ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) p).map
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)).app (op (⊤ : Opens X))

/-- The defining sheaf-cohomology expression for `moduleCohomologyMap`. -/
theorem moduleCohomologyMap_def
    {F G : X.Modules} (φ : F ⟶ G) (p : ℕ) :
    moduleCohomologyMap φ p =
      ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) p).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)).app (op (⊤ : Opens X)) := sorry

end AlgebraicGeometry.RingedSpace
