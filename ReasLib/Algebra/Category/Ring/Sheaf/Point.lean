module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Commutative-ring stalks at points of a site

The fiber functor of a site point already supplies the canonical stalk object.  This file gives
that object, and the map induced by a morphism of ring sheaves, their natural ring-theoretic names.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (p : GrothendieckTopology.Point.{w} J)

/-- The commutative-ring stalk of `𝒪` at the point `p`.  It is expressed through the canonical
presheaf fiber, so this owner is definitionally shared with module-stalk infrastructure. -/
@[stacks 04ET "commutative-ring stalk"]
abbrev stalkCommRing (𝒪 : Sheaf J CommRingCat.{w}) : CommRingCat.{w} :=
  p.presheafFiber.obj 𝒪.obj

/-- The map on commutative-ring stalks induced by a morphism of ring sheaves. -/
abbrev stalkCommRingMap {𝒪 𝒪' : Sheaf J CommRingCat.{w}} (f : 𝒪 ⟶ 𝒪') :
    p.stalkCommRing 𝒪 ⟶ p.stalkCommRing 𝒪' :=
  p.presheafFiber.map f.hom

end CategoryTheory.GrothendieckTopology.Point
