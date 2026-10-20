module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sheaves.Abelian

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} [NoetherianSpace X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]

/-- On a Noetherian space of topological Krull dimension at most `d`, the global
cohomology of every abelian sheaf vanishes in degrees strictly greater than `d`. -/
theorem isZero_higherCohomology_of_noetherianSpace_of_topologicalKrullDim_le
    (d : ℕ) (hXdim : topologicalKrullDim X ≤ d)
    (F : X.Sheaf AddCommGrpCat.{u}) {p : ℕ} (hp : d < p) :
    IsZero (F.H' p (⊤ : Opens X)) := sorry

end CategoryTheory.Sheaf
