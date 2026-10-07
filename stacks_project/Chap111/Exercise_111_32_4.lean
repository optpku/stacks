module

public import ReasLib.Topology.Sheaves.Pullback.Adjunction
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/- Exercise 111.32.4: for a continuous map `f : X ⟶ Y` of topological spaces, pushforward and
pullback of sheaves of sets form an adjoint pair, with pullback left adjoint to pushforward. -/
@[stacks 02EV]
#check (TopCat.Sheaf.typesPullbackPushforwardAdjunction f :
    TopCat.Sheaf.pullback (Type u) f ⊣ TopCat.Sheaf.pushforward (Type u) f)
