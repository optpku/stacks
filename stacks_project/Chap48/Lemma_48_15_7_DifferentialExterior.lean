/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.DifferentialExterior

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open DerivedCategory RingedSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Compatibility checks for the shared differential-exterior API. -/
#check
  (AlgebraicGeometry.SmoothOfRelativeDimension.differentialsIsFiniteLocallyFreeOfRank :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ),
      [SmoothOfRelativeDimension d f] →
      SheafOfModules.IsFiniteLocallyFreeOfRank d (Ω[f.toShHom]))

#check
  (AlgebraicGeometry.Scheme.Hom.differentialExteriorShift_mem :
      ∀ {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ),
      [SmoothOfRelativeDimension d f] →
      Scheme.ModuleDerived.quasicoherentProperty X
        (((singleFunctor X.Modules 0).obj
          (ExteriorPower.sheaf (Ω[f.toShHom]) d))⟦(d : ℤ)⟧))

#check
  (AlgebraicGeometry.Scheme.Hom.differentialExteriorShift :
      ∀ {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ),
      [SmoothOfRelativeDimension d f] →
      Scheme.DerivedQCoh X)

#check
  (AlgebraicGeometry.Scheme.Hom.differentialExteriorShift_obj :
      ∀ {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ),
      [SmoothOfRelativeDimension d f] →
      (AlgebraicGeometry.Scheme.Hom.differentialExteriorShift f d).obj =
        ((singleFunctor X.Modules 0).obj
          (ExteriorPower.sheaf (Ω[f.toShHom]) d))⟦(d : ℤ)⟧)
