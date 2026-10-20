module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Finite fppf/étale derived comparison of algebraic spaces

For a finite morphism, inverse image from the small étale site to the big fppf
slice commutes with bounded-below derived direct image via the canonical map.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FppfEtale

/-- For a finite morphism of algebraic spaces, the canonical derived base-change map
from the inverse image of small-étale derived direct image to big-fppf derived
direct image of the inverse image is an isomorphism for every bounded-below
complex of abelian small-étale sheaves. -/
theorem finite_derivedPushforward {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsFinite f]
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso (derivedBaseChangeApp f K) := sorry


attribute [instance] finite_derivedPushforward

end AlgebraicGeometry.AlgebraicSpace.FppfEtale

end

end
