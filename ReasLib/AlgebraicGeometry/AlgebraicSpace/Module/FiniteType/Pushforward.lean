module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a finite morphism of algebraic spaces over a scheme, a quasi-coherent module is of
finite type if and only if its pushforward is of finite type. -/
@[stacks 060Z]
theorem isFiniteType_iff_pushforward_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ℱ.IsFiniteType ↔ ((pushforward f).obj ℱ).IsFiniteType :=
  sorry

/-- Pushforward along a finite morphism preserves finite type of a
quasi-coherent module on an algebraic space. -/
instance pushforward_obj_isFiniteType_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] :
    ((pushforward f).obj ℱ).IsFiniteType :=
  (isFiniteType_iff_pushforward_of_isFinite f ℱ).mp inferInstance

end AlgebraicGeometry.AlgebraicSpace.Modules
