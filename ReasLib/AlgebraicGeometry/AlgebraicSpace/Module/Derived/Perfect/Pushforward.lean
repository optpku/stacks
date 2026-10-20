module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Perfect

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- The unbounded derived pushforward of a perfect object supported on the inverse image of the
reduced complement in an elementary distinguished square is perfect. -/
theorem IsPerfect.pushforwardDerived_of_isSupportedOn
    {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X)
    [IsElementaryDistinguishedSquare j f] {E : ModuleDerived V} (hE : IsPerfect E)
    (h_support : IsSupportedOn E (Points.map f ⁻¹' (toOpenSubspace j f).pointsSetᶜ)) :
    IsPerfect ((Modules.moduleDerivedPushforward f).obj E) :=
  sorry

/-- The unbounded derived pushforward of a perfect object along a perfect proper morphism
of algebraic spaces with Noetherian target is perfect. -/
@[stacks 0E4U]
theorem pushforwardDerived_isPerfect_of_perfect_of_proper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Perfect f] [Proper f] [IsNoetherian Y]
    (E : ModuleDerived X) (hE : IsPerfect E) :
    IsPerfect ((Modules.moduleDerivedPushforward f).obj E) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
