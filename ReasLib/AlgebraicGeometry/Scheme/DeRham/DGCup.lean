/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.ClassAction

@[expose] public section
open AlgebraicGeometry CategoryTheory
open RingedSite.Hom
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.DeRham.ClassAction

variable {X S : Scheme.{u}} (p : X ⟶ S)
variable [(moduleDerivedGlobalSections.{u}
  (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)).CommShift ℤ]

/-- The hypercohomology product obtained by composition in the derived category of
right de Rham DG modules, followed by evaluation on the regular-module unit. -/
def yonedaCup (n m : ℤ) (ξ : cohomology p n) (η : cohomology p m) :
    cohomology p (n + m) :=
  unitEvaluation p (n + m) ((dgLift p m η).comp (dgLift p n ξ) rfl)

/-- The product is the unit value of the DG lift of the second class followed by
the shifted DG lift of the first class. -/
theorem yonedaCup_eq (n m : ℤ) (ξ : cohomology p n) (η : cohomology p m) :
    yonedaCup p n m ξ η =
      unitEvaluation p (n + m) ((dgLift p m η).comp (dgLift p n ξ) rfl) := rfl

/-- Forgetting the DG-module action and taking cohomology identifies the action of
a class with the product defined by composition of its regular-module lifts. -/
theorem onCohomology_apply_yonedaCup (n m : ℤ)
    (ξ : cohomology p n) (η : cohomology p m) :
    (onCohomology p n m ξ).hom η = yonedaCup p n m ξ η := sorry

end AlgebraicGeometry.Scheme.DeRham.ClassAction
