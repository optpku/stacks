module

public import ReasLib.CategoryTheory.Sites.Topos.Morphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u₁ u₂ v₁ v₂ w

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f g : MorphismOfTopoiIn J K)

/- Definition 7.36.1: a 2-morphism from f to g is a transformation of
functors f.pushforward ⟶ g.pushforward. -/
@[stacks 04IA] #check (f.pushforward ⟶ g.pushforward)
