module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback

/-! Compatibility name for composition of module pushforwards. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Module pushforward along a composite is canonically identified with successive pushforwards. -/
abbrev pushforwardCompIso {X Y Z : AlgebraicSpace S} (α : X ⟶ Y) (β : Y ⟶ Z) :
    pushforward α ⋙ pushforward β ≅ pushforward (α ≫ β) :=
  pushforwardComp α β

end AlgebraicGeometry.AlgebraicSpace.Modules
