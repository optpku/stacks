module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.Topology.Category.TopCat.Subset

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

/-- If `Z` is closed in a spectral space `X` and each intersection
`Z ∩ closure ({x} : Set X)` is connected, restriction identifies global sections of every sheaf
on `X` with global sections on `Z`. -/
theorem globalSectionsBijectiveOfConnectedClosureIntersections
    {X : TopCat.{u}} [SpectralSpace X] {Z : Set X}
    (hZ : IsClosed Z)
    (hconn : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X)))
    (F : X.Sheaf (Type u)) :
    Function.Bijective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
        (TopCat.subsetInclusion Z)).unit.app F).hom.app (op (⊤ : Opens X))) := sorry

end TopCat.Sheaf

end
