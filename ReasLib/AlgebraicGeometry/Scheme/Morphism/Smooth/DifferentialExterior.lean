/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open DerivedCategory RingedSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SmoothOfRelativeDimension

/-- The relative differentials of a smooth morphism of relative dimension `d` are finite
locally free of rank `d`. -/
@[instance]
theorem differentialsIsFiniteLocallyFreeOfRank
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d f] :
    SheafOfModules.IsFiniteLocallyFreeOfRank d (Ω[f.toShHom]) := sorry

end AlgebraicGeometry.SmoothOfRelativeDimension

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- The degree-zero `d`th exterior power of the relative differentials, shifted by `d`,
has quasicoherent cohomology. -/
theorem differentialExteriorShift_mem (f : X ⟶ S) (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    Scheme.ModuleDerived.quasicoherentProperty X
      (((singleFunctor X.Modules 0).obj
        (ExteriorPower.sheaf (Ω[f.toShHom]) d))⟦(d : ℤ)⟧) := sorry

/-- The `d`th exterior power of the relative differentials, placed in degree zero and
shifted by `d`, as a quasicoherent derived object. -/
noncomputable def differentialExteriorShift (f : X ⟶ S) (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    Scheme.DerivedQCoh X :=
  ⟨((singleFunctor X.Modules 0).obj
      (ExteriorPower.sheaf (Ω[f.toShHom]) d))⟦(d : ℤ)⟧,
    differentialExteriorShift_mem f d⟩

/-- The underlying derived module of `differentialExteriorShift f d` is the explicit
shifted degree-zero exterior power of the relative differentials. -/
theorem differentialExteriorShift_obj (f : X ⟶ S) (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    (differentialExteriorShift f d).obj =
      ((singleFunctor X.Modules 0).obj
        (ExteriorPower.sheaf (Ω[f.toShHom]) d))⟦(d : ℤ)⟧ := sorry

end AlgebraicGeometry.Scheme.Hom
