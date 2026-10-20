module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification.OverAbelian

/-!
# Small étale ringed site of an algebraic space

The structure sheaf `𝒪_X` on the small étale site of an algebraic space `X` is the
global-sections sheaf `U ↦ Γ(U, 𝒪_U)`. This packages the ringed site `(X_étale, 𝒪_X)` and
its category of module sheaves.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The small étale site of `X`, equipped with its structure sheaf. -/
abbrev ringedSite {S : Scheme.{u}} (X : AlgebraicSpace S) : RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf (smallEtaleTopology X) (structureSheaf X)

/-- The structure sheaf of `ringedSite X` is `𝒪_X`. -/
theorem ringedSite_structureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (ringedSite X).structureSheaf = structureSheaf X :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
