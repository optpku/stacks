module

public import ReasLib.CategoryTheory.Sites.Topos.Morphism
public import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical mates between morphisms of topoi

An isomorphism between inverse-image functors canonically determines an isomorphism between
their right adjoints.  Keeping this mate as explicit data is the neutral bridge used to turn
commutative inverse-image diagrams into reusable direct-image `2`-cells.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The canonical right-adjoint mate of an isomorphism between the inverse images of two
morphisms of topoi. -/
@[stacks 04J1 "right-adjoint mate"]
noncomputable def pushforwardIsoOfInverseImageIso
    (f g : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, w} J K)
    (e : f.inverseImage ≅ g.inverseImage) :
    f.pushforward ≅ g.pushforward :=
  (f.adjunction.ofNatIsoLeft e).rightAdjointUniq g.adjunction

-- The comparison is the uniqueness isomorphism between two explicitly displayed right
-- adjoints and therefore introduces no witness choice beyond the canonical adjunction API.

end CategoryTheory.MorphismOfTopoiIn
