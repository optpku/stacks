module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.LocalGeneration
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.Hom

/-- Finite type of a module sheaf descends along an open, surjective, flat morphism of
locally ringed spaces. -/
@[stacks 09UB]
theorem isFiniteType_of_pullback {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (ℱ : Y.Modules) (h_open : IsOpenMap f.base)
    (h_surjective : Function.Surjective f.base) [RingedSpace.Hom.IsFlat f.toShHom]
    [((RingedSpace.Hom.pullback f.toShHom).obj ℱ).IsFiniteType] :
    ℱ.IsFiniteType := sorry

end AlgebraicGeometry.LocallyRingedSpace.Hom
