module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a finite morphism of schemes, a quasi-coherent module is of finite type if and
only if its pushforward is of finite type. -/
@[stacks 05B3]
theorem isFiniteType_iff_pushforward_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ℱ.IsFiniteType ↔ ((Scheme.Modules.pushforward f).obj ℱ).IsFiniteType := sorry

/-- Pushforward along a finite morphism preserves finite type for quasi-coherent scheme
modules. -/
instance pushforward_obj_isFiniteType_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] :
    ((Scheme.Modules.pushforward f).obj ℱ).IsFiniteType := sorry

end AlgebraicGeometry.Scheme.Modules
