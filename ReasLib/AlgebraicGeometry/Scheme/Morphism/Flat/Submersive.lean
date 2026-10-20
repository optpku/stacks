module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A flat, quasi-compact, surjective morphism of schemes is submersive. -/
instance instSubmersiveOfFlatOfQuasiCompactOfSurjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f] [Surjective f] :
    Submersive f := sorry

end AlgebraicGeometry
