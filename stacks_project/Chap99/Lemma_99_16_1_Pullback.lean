module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange.Pullback

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

noncomputable section

universe u

/- Derived base-change compatibility API. -/
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.baseChangeSpaceMap :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V V' : AlgebraicSpace S} {g : V ⟶ Y} {g' : V' ⟶ Y}
    (φ : V' ⟶ V) (hφ : φ ≫ g = g'),
    Limits.pullback f g' ⟶ Limits.pullback f g)
