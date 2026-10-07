module

public import ReasLib.CategoryTheory.Sites.Topos.Morphism
public import Mathlib.CategoryTheory.Sites.Types
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Definition 7.32.1: let (C, J) be a site. A point of the topos Sh(C, J) is a
morphism of topoi p : Sh(pt) ⟶ Sh(C, J). This is the specialized type
`MorphismOfTopoiIn J typesGrothendieckTopology`, where Sh(pt) is the sheaf
topos of `typesGrothendieckTopology` (equivalent to Type via `typeEquiv`). -/
@[stacks 00Y4] #check MorphismOfTopoiIn J typesGrothendieckTopology.{w}

#check typesGrothendieckTopology.{w}
#check typeEquiv.{w}
