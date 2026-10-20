module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.Proper
import StacksCheckRecall

/-!
# Lemma 84.6.5

For a proper morphism of algebraic spaces, small-étale to big-fppf inverse
image commutes with direct image on sheaves of sets and with bounded-below
derived direct image on complexes with locally torsion cohomology.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Sheaf
open AlgebraicGeometry.AlgebraicSpace.FppfEtale

universe u

/- Lemma 84.6.5: proper direct image commutes with small-étale to big-fppf
inverse image on sheaves of sets and on torsion bounded-below complexes. -/
@[stacks 0DGJ]
#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.proper_smallFppfPushforward_isIso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f],
    IsIso (smallFppfPushforwardHom f))

#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.proper_derivedPushforward :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) K),
    IsIso (derivedBaseChangeApp f K))

end
