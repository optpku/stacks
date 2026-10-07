module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeRegularImmersion

/-!
# Pointwise flatness along relative quasi-regular immersions

A morphism is flat at the image of a point on a relative quasi-regular immersion when the
corresponding local ring of the ambient scheme is Noetherian.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RelativeQuasiRegularImmersion

variable {X S Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}

/-- A morphism is flat at the image of a point on a relative quasi-regular immersion if the
local ring of the ambient scheme at that image is Noetherian. -/
@[stacks 063T]
theorem flatAt [RelativeQuasiRegularImmersion f i] (x : Z)
    [IsNoetherianRing (X.presheaf.stalk (i.base x))] :
    Scheme.Hom.flatAt f (i.base x) := sorry

end AlgebraicGeometry.RelativeQuasiRegularImmersion
