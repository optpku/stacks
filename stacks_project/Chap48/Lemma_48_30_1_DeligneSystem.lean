module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

variable {X U : Scheme.{v}} {j : U ⟶ X}
variable [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]

#check (@AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.stage X U j _ _ _ :
  AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem j → ℕ+ → DerivedCategory X.Modules)
