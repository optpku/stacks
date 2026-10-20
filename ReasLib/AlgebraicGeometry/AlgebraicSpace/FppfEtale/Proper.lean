module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion

/-!
# Proper fppf/étale direct-image comparisons

Proper direct image commutes with small-étale to big-fppf inverse image on
sheaves of sets and on bounded-below complexes with locally torsion cohomology.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FppfEtale

/-- For a proper morphism of algebraic spaces, the canonical small-étale to
big-fppf direct-image comparison on sheaves of sets is an isomorphism. -/
instance proper_smallFppfPushforward_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f] :
    IsIso (smallFppfPushforwardHom f) := sorry

/-- For a proper morphism of algebraic spaces, the canonical small-étale to
big-fppf derived direct-image comparison is an isomorphism on bounded-below
complexes with locally torsion cohomology. -/
theorem proper_derivedPushforward {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f]
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) K) :
    IsIso (derivedBaseChangeApp f K) := sorry

/-- The proper small-étale to big-fppf derived comparison is invertible when
local torsion of the bounded-below complex's cohomology is supplied as a fact. -/
instance proper_derivedPushforward_isIso_of_fact
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    [hK : Fact (DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) K)] :
    IsIso (derivedBaseChangeApp f K) :=
  proper_derivedPushforward f K hK.out

end AlgebraicGeometry.AlgebraicSpace.FppfEtale

end

end
