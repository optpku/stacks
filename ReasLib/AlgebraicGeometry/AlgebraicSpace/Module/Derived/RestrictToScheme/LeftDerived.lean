module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived

/-! # Total left-derived restriction to an underlying scheme

Restriction of modules to the underlying scheme induces a total left-derived functor
whenever its homotopy-category functor admits a left-derived functor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Restriction of modules from `ofOver U` to the underlying scheme is additive. -/
instance instAdditive_restrictToScheme {S : Scheme.{u}} (U : Over S) :
    (Modules.restrictToScheme U).Additive :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}}

/-- Derived restriction of `D(𝒪_{ofOver U})` to the Zariski derived category of the
underlying scheme. -/
def restrictToSchemeDerived (U : Over S)
    [(Functor.Homotopy.toDerived (Modules.restrictToScheme U)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules (ofOver U)) (ComplexShape.up ℤ))] :
    ModuleDerived (ofOver U) ⥤ DerivedCategory U.left.Modules :=
  Functor.LeftDerived.Homotopy.functor (Modules.restrictToScheme U)

/-- Derived restriction to the underlying scheme is the total left derived functor of
`Modules.restrictToScheme`. -/
theorem restrictToSchemeDerived_eq (U : Over S)
    [(Functor.Homotopy.toDerived (Modules.restrictToScheme U)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules (ofOver U)) (ComplexShape.up ℤ))] :
    restrictToSchemeDerived U =
      Functor.LeftDerived.Homotopy.functor (Modules.restrictToScheme U) := rfl


/-- The Zariski derived category of a scheme agrees with the derived category of modules
on the underlying ringed space. -/
theorem derivedCategory_modules_eq_ringedSpace (X : Scheme.{u}) :
    DerivedCategory X.Modules = RingedSpace.ModuleDerived X.toRingedSpace := rfl

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
