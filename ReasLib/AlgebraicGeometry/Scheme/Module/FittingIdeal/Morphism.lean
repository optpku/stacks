module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FittingIdeal.Flattening
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ModulePullback

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ModuleRestriction ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism between perfect scheme modules of Tor dimension at most one that both vanish
on a scheme-theoretically dense open has, after one admissible blowup, perfect kernel, image,
and cokernel, each of Tor dimension at most one. -/
theorem exists_isAdmissibleBlowup_kernel_image_cokernel {X : Scheme.{u}} {F G : X.Modules}
    (φ : F ⟶ G) (U : X.Opens)
    (hPerfectF : SheafOfModules.IsPerfect F)
    (hTorF : RingedSpace.ModuleHasTorDimensionLE F 1)
    (hPerfectG : SheafOfModules.IsPerfect G)
    (hTorG : RingedSpace.ModuleHasTorDimensionLE G 1)
    (hDense : schemeTheoreticallyDense U)
    (hZeroF : IsZero (F.over U)) (hZeroG : IsZero (G.over U)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
      IsAdmissibleBlowup U b ∧
        (SheafOfModules.IsPerfect (kernel ((Scheme.Modules.pullback b).map φ)) ∧
          RingedSpace.ModuleHasTorDimensionLE
            (kernel ((Scheme.Modules.pullback b).map φ)) 1) ∧
        (SheafOfModules.IsPerfect (image ((Scheme.Modules.pullback b).map φ)) ∧
          RingedSpace.ModuleHasTorDimensionLE
            (image ((Scheme.Modules.pullback b).map φ)) 1) ∧
        (SheafOfModules.IsPerfect (cokernel ((Scheme.Modules.pullback b).map φ)) ∧
          RingedSpace.ModuleHasTorDimensionLE
            (cokernel ((Scheme.Modules.pullback b).map φ)) 1) := sorry

end AlgebraicGeometry.Scheme.Modules
