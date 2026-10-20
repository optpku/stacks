module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport.Proper

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite-type quasicoherent module on the source of a proper morphism is universally pure
relative to the target. -/
theorem isUniversallyPureOver_of_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    F.IsUniversallyPureOver f := sorry

/-- A finite-type quasicoherent module whose support is proper over the base is universally pure
relative to the base. -/
theorem isUniversallyPureOver_of_hasProperSupportOver
    {X S : Scheme.{u}} (f : X ⟶ S) [f.FiniteType]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    [HasProperSupportOver f F] :
    F.IsUniversallyPureOver f := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- The structure sheaf of the source of a proper morphism is universally pure relative to the
target. -/
theorem isUniversallyPureOver_of_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] :
    Modules.IsUniversallyPureOver
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) f := sorry

end AlgebraicGeometry.Scheme
