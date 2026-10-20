module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.DerivedCategory.DerivedTensor

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect

/-- An absolutely perfect derived module on the source of a flat, locally finitely presented
morphism of algebraic spaces is perfect relative to that morphism. -/
theorem isPerfectRelativeTo {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    {K : ModuleDerived X} (hK : IsPerfect K) :
    IsPerfectRelativeTo f K := sorry

/-- Tensoring a relatively perfect derived module on the left by an absolutely perfect derived
module preserves perfectness relative to a flat, locally finitely presented morphism of
algebraic spaces. -/
theorem tensor_isPerfectRelativeTo {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    {K M : ModuleDerived X} (hK : IsPerfect K) (hM : IsPerfectRelativeTo f M) :
    IsPerfectRelativeTo f (K ⊗ᴸ M) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect
