module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.LinearAlgebra.Dimension.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Generic rank under dominant pullback

The cardinal generic rank of a quasi-coherent module on an integral scheme is
invariant under pullback along a dominant morphism of integral schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback along a dominant morphism of integral schemes preserves the cardinal dimension
of the generic stalk of a quasi-coherent module over the function field. -/
@[stacks 0HAH]
theorem pullback_rank_eq {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (𝒢 : Y.Modules) [𝒢.IsQuasicoherent] :
    Module.rank Y.functionField (RingedSpace.stalkModuleCat 𝒢 (genericPoint Y)) =
      Module.rank X.functionField
        (RingedSpace.stalkModuleCat ((pullback f).obj 𝒢) (genericPoint X)) := sorry

end AlgebraicGeometry.Scheme.Modules
