module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward

/-!
# Pushforward of ideal-torsion subsheaves

This file records the compatibility of ideal-torsion subsheaves with pushforward of
quasi-coherent module sheaves.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a quasi-compact and quasi-separated morphism of schemes, pushforward carries the
subsheaf annihilated by the pulled-back finite type ideal sheaf to the subsheaf annihilated by
the original ideal sheaf, sectionwise on every open. -/
theorem range_pushforward_idealTorsionSubsheafι_app_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (I : Y.IdealSheafData)
    [((Subobject.underlying.obj I.toSubobject : Y.Modules).IsFiniteType)]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (U : Y.Opens) :
    Set.range (((pushforward f).map
        (idealTorsionSubsheafι (I.comap f) ℱ)).app U) =
      Set.range ((idealTorsionSubsheafι I ((pushforward f).obj ℱ)).app U) := sorry

end AlgebraicGeometry.Scheme.Modules
