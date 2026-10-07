module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.LocalGeneration
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.Quasicoherent

/-!
# Base change of Fitting ideal sheaves

The Fitting ideal sheaf of a finite-type quasi-coherent scheme module commutes with pullback
along an arbitrary morphism of schemes.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}}

/-- Pulling back the `i`th Fitting ideal sheaf of a finite-type quasi-coherent module along a
scheme morphism gives the `i`th Fitting ideal sheaf of the pulled-back module. -/
theorem fittingIdealSheaf_pullback
    (f : T ⟶ S) (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (i : ℕ) :
    (fittingIdealSheaf ℱ i).comap f =
      fittingIdealSheaf ((Modules.pullback f).obj ℱ) i := sorry

/-- On every affine open, pullback of the `i`th Fitting ideal sheaf and the `i`th Fitting ideal
sheaf of the pulled-back module determine the same ideal. -/
@[simp]
theorem fittingIdealSheaf_pullback_ideal
    (f : T ⟶ S) (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    (i : ℕ) (U : T.affineOpens) :
    ((fittingIdealSheaf ℱ i).comap f).ideal U =
      (fittingIdealSheaf ((Modules.pullback f).obj ℱ) i).ideal U := by
  simpa using
    congrArg (fun I ↦ I.ideal U) (fittingIdealSheaf_pullback f ℱ i)

end AlgebraicGeometry.Scheme
