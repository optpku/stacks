module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.BaseChange
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 31.9.1: for every morphism of schemes `f : T ⟶ S` and every finite-type
quasi-coherent `S`-module `ℱ`, pullback of the `i`th Fitting ideal sheaf is the `i`th
Fitting ideal sheaf of `(Scheme.Modules.pullback f).obj ℱ`. -/
@[stacks 0C3D] #check
  (AlgebraicGeometry.Scheme.fittingIdealSheaf_pullback :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S) (ℱ : S.Modules)
      [ℱ.IsFiniteType] [ℱ.IsQuasicoherent] (i : ℕ),
      (AlgebraicGeometry.Scheme.fittingIdealSheaf ℱ i).comap f =
        AlgebraicGeometry.Scheme.fittingIdealSheaf
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj ℱ) i)
