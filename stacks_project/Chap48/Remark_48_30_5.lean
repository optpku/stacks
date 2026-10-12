/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.ExtensionByZero
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open DerivedCategory.Bounded.CohomologyIn
open DerivedCategory.TStructure
open scoped DerivedCategory.CohomologyIn

universe v

/- Remark 48.30.5 -/
@[stacks 0G4N] #check
  (@AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero :
    ∀ {X U : Scheme.{v}} (j : U ⟶ X) [IsNoetherian X] [IsNoetherian U]
      [IsOpenImmersion j],
      Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf] ⥤
        Pro Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])

set_option synthInstance.maxHeartbeats 100000 in
/- Remark 48.30.5 -/
@[stacks 0G4N] #check
  (@AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero_exact :
    ∀ {X U : Scheme.{v}} (j : U ⟶ X) [IsNoetherian X] [IsNoetherian U]
      [IsOpenImmersion j]
      (T : Pretriangulated.Triangle
        Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]),
      T ∈ Pretriangulated.distinguishedTriangles →
      Nonempty (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.ExactTrianglePresentation j T))

/- Remark 48.30.5 -/
@[stacks 0G4N] #check
  (@AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZeroHomMap_bijective :
    ∀ {X U : Scheme.{v}} (j : U ⟶ X) [IsNoetherian X] [IsNoetherian U]
      [IsOpenImmersion j]
      (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
      (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]),
      Function.Bijective
        (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZeroHomMap j K L))
