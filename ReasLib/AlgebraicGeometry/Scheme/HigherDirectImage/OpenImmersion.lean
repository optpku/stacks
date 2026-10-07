module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HigherDirectImage

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Positive higher direct images of a quasi-coherent module along a quasi-compact open immersion
vanish when every stalk ring of the target is at most one-dimensional. -/
theorem isZero_of_quasiCompact_open_of_stalk_ringKrullDim_le_one
    (hDim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1)
    (U : X.Opens) [QuasiCompact U.ι]
    (ℱ : (U : Scheme).Modules) [ℱ.IsQuasicoherent]
    (p : ℕ) (hp : 0 < p) :
    IsZero (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule U.ι.toShHom ℱ p) := sorry

/-- Coherence of the higher direct images of the structure sheaf below a bound
implies coherence in those degrees for every finite locally free module. -/
theorem isCoherent_of_finiteLocallyFree
    (U : X.Opens) (n : ℕ)
    (hO : ∀ p : ℕ, p < n →
      (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule U.ι.toShHom
        (SheafOfModules.unit U.toScheme.ringCatSheaf : U.toScheme.Modules) p).IsCoherent) :
    ∀ (F : U.toScheme.Modules) [SheafOfModules.IsFiniteLocallyFree F] (p : ℕ), p < n →
      (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule U.ι.toShHom F p).IsCoherent := sorry

end AlgebraicGeometry.Scheme.HigherDirectImage
